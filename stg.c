/*
 * stg.c - STG Machine for SKI Combinators
 *
 * This is a proper Spineless Tagless G-machine implementation:
 * - Spineless: Arguments passed on stack, not in spine
 * - Tagless: No runtime tag inspection, dispatch via entry code pointer
 * - G-machine: Graph reduction with sharing via self-updating thunks
 *
 * The key insight from SPJ's 1992 paper:
 * - "Tagless" means no interpretive switch/case dispatch
 * - Each closure has an entry code pointer - we call/jump to it directly
 * - This eliminates the "spine" of the G-machine's central eval loop
 *
 * Closure layout: [entry_ptr | payload...]
 *   entry_ptr: Function pointer to entry code for this closure type
 *   payload: Type-specific data (captured variables, etc.)
 *
 * Entry code contract:
 *   - Receives: STG machine state, current closure
 *   - Either: consumes args from stack and tail-calls next closure
 *   - Or: returns a result (closure in WHNF)
 */

#include "stg.h"
#include "io.h"
#include <libeezo/term.h>
#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <setjmp.h>

#define HEAP_SIZE   (16 * 1024 * 1024)  /* 16MB per semi-space */
#define STACK_SIZE  (256 * 1024)
#define WORD        sizeof(void*)

/* Forward declarations */
struct Closure;
struct STG;
struct WorkStack;
struct ConvStack;

/*
 * Entry code function type - this is the "tagless" dispatch mechanism
 * Instead of switch(tag), we call closure->entry(stg, closure)
 */
typedef struct Closure *(*EntryCode)(struct STG *stg, struct Closure *self);

/*
 * Closure in memory - TRUE STG layout
 * First word is always the entry code pointer (tagless!)
 */
typedef struct Closure {
    EntryCode entry;      /* Entry code - NO TAG, just jump here */
    union {
        struct { struct Closure *x; } s1;           /* S x */
        struct { struct Closure *x, *y; } s2;       /* S x y */
        struct { struct Closure *x; } k1;           /* K x */
        struct { struct Closure *f, *arg; } ap;     /* f @ arg */
        struct { struct Closure *target; } ind;     /* -> target (also used as forwarding ptr) */
    } payload;
} Closure;

/*
 * STG Machine State with Cheney GC
 */
typedef struct STG {
    /* Two semi-spaces for copying GC */
    Closure *space[2];    /* base of each semi-space */
    int active_space;     /* which space is currently active (0 or 1) */
    Closure *hp;          /* heap allocation pointer */
    Closure *heap_end;    /* end of current semi-space */
    size_t heap_size;     /* size of each semi-space */
    
    Closure **stack;      /* argument stack */
    Closure **sp;         /* stack pointer (grows down) */
    Closure **stack_base;
    
    /* Current node being evaluated - needed for GC roots */
    Closure *current_node;
    
    /* Extra GC roots: C-held closure pointers that must survive a GC
     * triggered by stg_reserve(). Callers stash pointers here before
     * reserving and reload them afterwards. */
    Closure *extra_roots[4];
    struct WorkStack *ws_root;   /* live normalizer work stack, or NULL */
    struct ConvStack *cs_root;   /* live term_to_stg conversion stack, or NULL */
    
    /* Update frames: pushed when an AP thunk is entered; popped when a
     * value is returned to it, at which point the thunk is overwritten
     * with an IND to the value (sharing). saved_sp is the arg-stack
     * pointer at push time and acts as a BARRIER: args below it belong
     * to enclosing evaluations and are invisible until the frame pops. */
    struct {
        Closure *thunk;
        Closure **saved_sp;
    } *update_stack;
    int update_sp;
    int update_size;
    
    /* Trampoline: an entry code that wants to tail-call sets `next` and
     * returns NULL; stg_enter loops instead of growing the C stack. */
    Closure *next;
    
    /* Normalization mode: 0 = full normal form, 1 = weak head normal form */
    int whnf;
    
    /* For returning to C */
    jmp_buf exit_jmp;
    Closure *result;
    
    /* Pre-built primitive closures (shared singletons) */
    Closure *prim_S;
    Closure *prim_K;
    Closure *prim_I;
    
    /* GC statistics */
    u64 gc_count;
    u64 bytes_copied;
    
    /* Reduction step counter and optional bound */
    i64 steps;
    i64 max_steps;  /* 0 = unlimited */
} STG;

static STG *g_stg = NULL;

/* Forward declarations of entry codes */
static Closure *entry_S(STG *stg, Closure *self);
static Closure *entry_K(STG *stg, Closure *self);
static Closure *entry_I(STG *stg, Closure *self);
static Closure *entry_S1(STG *stg, Closure *self);
static Closure *entry_S2(STG *stg, Closure *self);
static Closure *entry_K1(STG *stg, Closure *self);
static Closure *entry_AP(STG *stg, Closure *self);
static Closure *entry_IND(STG *stg, Closure *self);

/* Special marker for forwarding pointers during GC */
static Closure *entry_FWD(STG *stg, Closure *self) {
    (void)stg;
    /* This should never be called - it's a forwarding pointer */
    fprintf(stderr, "GC error: tried to enter forwarding pointer\n");
    return self;
}

/* Forward declaration for GC */
static void stg_gc(STG *stg);
static Closure *gc_copy(STG *stg, Closure *from, Closure **to_hp);

/*
 * Get size of closure in words based on entry code
 */
static int closure_size(Closure *c) {
    if (c->entry == entry_S || c->entry == entry_K || c->entry == entry_I) {
        return 1;  /* just entry ptr */
    }
    if (c->entry == entry_S1 || c->entry == entry_K1 || c->entry == entry_IND) {
        return 2;  /* entry + 1 pointer */
    }
    if (c->entry == entry_S2 || c->entry == entry_AP) {
        return 3;  /* entry + 2 pointers */
    }
    if (c->entry == entry_FWD) {
        return 2;  /* forwarding pointer */
    }
    return 1;  /* unknown, assume minimal */
}

/*
 * Allocate on heap - triggers GC if needed
 */
static Closure *stg_alloc(STG *stg, int words) {
    Closure *p = stg->hp;
    Closure *new_hp = (Closure*)((char*)stg->hp + words * WORD);
    
    if ((char*)new_hp >= (char*)stg->heap_end) {
        /* Trigger garbage collection */
        stg_gc(stg);
        
        /* Try again after GC */
        p = stg->hp;
        new_hp = (Closure*)((char*)stg->hp + words * WORD);
        
        if ((char*)new_hp >= (char*)stg->heap_end) {
            fprintf(stderr, "STG: heap overflow after GC (need %d words)\n", words);
            longjmp(stg->exit_jmp, 1);
        }
    }
    
    stg->hp = new_hp;
    return p;
}

/*
 * Ensure `words` words can be allocated WITHOUT a GC.
 * Call this BEFORE loading closure pointers into C locals (pops, self
 * payload reads); everything still on the arg stack / in roots survives
 * the collection this may trigger. Subsequent stg_alloc calls totalling
 * `words` are then GC-free.
 */
static void stg_reserve(STG *stg, int words) {
    Closure *new_hp = (Closure*)((char*)stg->hp + words * WORD);
    if ((char*)new_hp >= (char*)stg->heap_end) {
        stg_gc(stg);
        new_hp = (Closure*)((char*)stg->hp + words * WORD);
        if ((char*)new_hp >= (char*)stg->heap_end) {
            fprintf(stderr, "STG: heap overflow after GC (need %d words)\n", words);
            longjmp(stg->exit_jmp, 1);
        }
    }
}

/*
 * Push to argument stack
 */
static void stg_push(STG *stg, Closure *c) {
    if (stg->sp <= stg->stack) {
        fprintf(stderr, "STG: stack overflow\n");
        longjmp(stg->exit_jmp, 1);
    }
    *--stg->sp = c;
}

/*
 * Arg-stack barrier: args below the topmost update frame belong to an
 * enclosing evaluation and must not be consumed by the current one.
 */
static Closure **stg_barrier(STG *stg) {
    return stg->update_sp > 0 ? stg->update_stack[stg->update_sp - 1].saved_sp
                              : stg->stack_base;
}

/*
 * Pop from argument stack (never past the barrier)
 */
static Closure *stg_pop(STG *stg) {
    if (stg->sp >= stg_barrier(stg)) {
        return NULL;  /* no args visible */
    }
    return *stg->sp++;
}

/*
 * Number of args visible above the barrier
 */
static int stg_stack_size(STG *stg) {
    return (int)(stg_barrier(stg) - stg->sp);
}

/*
 * Push an update frame for thunk `t` (current sp becomes its barrier)
 */
static void stg_push_update(STG *stg, Closure *t) {
    if (stg->update_sp >= stg->update_size) {
        stg->update_size *= 2;
        stg->update_stack = realloc(stg->update_stack,
                                    stg->update_size * sizeof(stg->update_stack[0]));
        if (!stg->update_stack) {
            fprintf(stderr, "STG: update stack realloc failed\n");
            exit(1);
        }
    }
    stg->update_stack[stg->update_sp].thunk = t;
    stg->update_stack[stg->update_sp].saved_sp = stg->sp;
    stg->update_sp++;
}

/*
 * Tail call: request that stg_enter continue with `c`
 */
static Closure *stg_tail(STG *stg, Closure *c) {
    stg->next = c;
    return NULL;
}

/* ========================================================================
 * ENTRY CODES - The heart of tagless STG
 * 
 * Each closure type has its own entry code. No switch/case dispatch!
 * We simply call: closure->entry(stg, closure)
 * 
 * Contract:
 *   - If enough args: consume them, build result, tail-call into next closure
 *   - If not enough: build PAP and return it (we're in WHNF)
 * ======================================================================== */

/*
 * S combinator entry code
 * S x y z → x z (y z)
 * Needs 3 arguments
 */
static Closure *entry_S(STG *stg, Closure *self) {
    (void)self;  /* S is a singleton, no payload */
    
    int n = stg_stack_size(stg);
    if (n < 3) {
        /* Not enough args - build PAP */
        if (n == 0) {
            return stg->prim_S;
        } else if (n == 1) {
            stg_reserve(stg, 2);
            Closure *x = stg_pop(stg);
            Closure *s1 = stg_alloc(stg, 2);
            s1->entry = entry_S1;
            s1->payload.s1.x = x;
            return s1;
        } else { /* n == 2 */
            stg_reserve(stg, 3);
            Closure *x = stg_pop(stg);
            Closure *y = stg_pop(stg);
            Closure *s2 = stg_alloc(stg, 3);
            s2->entry = entry_S2;
            s2->payload.s2.x = x;
            s2->payload.s2.y = y;
            return s2;
        }
    }
    
    /* Have 3 args: S x y z → x z (y z) */
    stg->steps++;
    if (stg->max_steps && stg->steps >= stg->max_steps) {
        longjmp(stg->exit_jmp, 2);  /* step limit exceeded */
    }
    stg_reserve(stg, 3);
    Closure *x = stg_pop(stg);
    Closure *y = stg_pop(stg);
    Closure *z = stg_pop(stg);
    
    /* Build thunk for (y z) */
    Closure *yz = stg_alloc(stg, 3);
    yz->entry = entry_AP;
    yz->payload.ap.f = y;
    yz->payload.ap.arg = z;
    
    /* Push args for x: first (y z), then z (z is first arg) */
    stg_push(stg, yz);
    stg_push(stg, z);
    
    /* Tail-call into x */
    return stg_tail(stg, x);
}

/*
 * S1 entry code (S with 1 captured arg)
 * (S x) y z → x z (y z)
 * Needs 2 more arguments
 */
static Closure *entry_S1(STG *stg, Closure *self) {
    int n = stg_stack_size(stg);
    if (n < 2) {
        if (n == 0) {
            return self;
        } else { /* n == 1 */
            stg->current_node = self;
            stg_reserve(stg, 3);
            self = stg->current_node;
            Closure *y = stg_pop(stg);
            Closure *s2 = stg_alloc(stg, 3);
            s2->entry = entry_S2;
            s2->payload.s2.x = self->payload.s1.x;
            s2->payload.s2.y = y;
            return s2;
        }
    }
    
    stg->steps++;
    if (stg->max_steps && stg->steps >= stg->max_steps) {
        longjmp(stg->exit_jmp, 2);
    }
    stg->current_node = self;
    stg_reserve(stg, 3);
    self = stg->current_node;
    Closure *x = self->payload.s1.x;
    Closure *y = stg_pop(stg);
    Closure *z = stg_pop(stg);
    
    Closure *yz = stg_alloc(stg, 3);
    yz->entry = entry_AP;
    yz->payload.ap.f = y;
    yz->payload.ap.arg = z;
    
    stg_push(stg, yz);
    stg_push(stg, z);
    
    return stg_tail(stg, x);
}

/*
 * S2 entry code (S with 2 captured args)
 * (S x y) z → x z (y z)
 * Needs 1 more argument
 */
static Closure *entry_S2(STG *stg, Closure *self) {
    if (stg_stack_size(stg) < 1) {
        return self;
    }
    
    stg->steps++;
    if (stg->max_steps && stg->steps >= stg->max_steps) {
        longjmp(stg->exit_jmp, 2);
    }
    stg->current_node = self;
    stg_reserve(stg, 3);
    self = stg->current_node;
    Closure *x = self->payload.s2.x;
    Closure *y = self->payload.s2.y;
    Closure *z = stg_pop(stg);
    
    Closure *yz = stg_alloc(stg, 3);
    yz->entry = entry_AP;
    yz->payload.ap.f = y;
    yz->payload.ap.arg = z;
    
    stg_push(stg, yz);
    stg_push(stg, z);
    
    return stg_tail(stg, x);
}

/*
 * K combinator entry code
 * K x y → x
 * Needs 2 arguments
 */
static Closure *entry_K(STG *stg, Closure *self) {
    (void)self;
    
    int n = stg_stack_size(stg);
    if (n < 2) {
        if (n == 0) {
            return stg->prim_K;
        } else { /* n == 1 */
            stg_reserve(stg, 2);
            Closure *x = stg_pop(stg);
            Closure *k1 = stg_alloc(stg, 2);
            k1->entry = entry_K1;
            k1->payload.k1.x = x;
            return k1;
        }
    }
    
    stg->steps++;
    if (stg->max_steps && stg->steps >= stg->max_steps) {
        longjmp(stg->exit_jmp, 2);
    }
    Closure *x = stg_pop(stg);
    stg_pop(stg);  /* discard y */
    
    return stg_tail(stg, x);
}

/*
 * K1 entry code (K with 1 captured arg)
 * (K x) y → x
 * Needs 1 more argument
 */
static Closure *entry_K1(STG *stg, Closure *self) {
    if (stg_stack_size(stg) < 1) {
        return self;
    }
    
    stg->steps++;
    if (stg->max_steps && stg->steps >= stg->max_steps) {
        longjmp(stg->exit_jmp, 2);
    }
    stg_pop(stg);  /* discard y */
    Closure *x = self->payload.k1.x;
    
    return stg_tail(stg, x);
}

/*
 * I combinator entry code
 * I x → x
 * Needs 1 argument
 */
static Closure *entry_I(STG *stg, Closure *self) {
    (void)self;
    
    if (stg_stack_size(stg) < 1) {
        return stg->prim_I;
    }
    
    Closure *x = stg_pop(stg);
    return stg_tail(stg, x);
}

/*
 * Application thunk entry code
 * (f arg) → push update frame for self, push arg, enter f
 *
 * The frame's barrier hides any args already on the stack, so f sees
 * exactly `arg`; when f's evaluation returns a value with the barrier
 * reached, stg_enter overwrites self with IND -> value and pops the
 * frame, then applies the value to the args that became visible.
 */
static Closure *entry_AP(STG *stg, Closure *self) {
    Closure *f = self->payload.ap.f;
    Closure *arg = self->payload.ap.arg;
    
    stg_push_update(stg, self);
    stg_push(stg, arg);
    return stg_tail(stg, f);
}

/*
 * Indirection entry code
 * Follows the indirection chain
 */
static Closure *entry_IND(STG *stg, Closure *self) {
    Closure *target = self->payload.ind.target;
    return stg_tail(stg, target);
}

/*
 * Enter a closure - THE ONLY DISPATCH POINT
 * This is now just a single indirect call, not a switch!
 */
static Closure *stg_enter(STG *stg, Closure *c) {
    for (;;) {
        stg->current_node = c;  /* Mark as GC root */
        Closure *v = c->entry(stg, c);
        if (!v) {
            c = stg->next;      /* tail call requested */
            continue;
        }
        
        /* v is a value w.r.t. the args above the top update frame. An
         * entry returns a value only when it has consumed every visible
         * arg, so sp == barrier: pop the frames whose evaluation this
         * value completes and update their thunks. */
        while (stg->update_sp > 0 &&
               stg->update_stack[stg->update_sp - 1].saved_sp == stg->sp) {
            Closure *t = stg->update_stack[stg->update_sp - 1].thunk;
            stg->update_sp--;
            if (t != v) {
                t->entry = entry_IND;
                t->payload.ind.target = v;
            }
        }
        
        /* Popping frames may have exposed enclosing args: apply v to them */
        if (stg_stack_size(stg) > 0) {
            c = v;
            continue;
        }
        
        stg->current_node = v;  /* Update root after reduction */
        return v;
    }
}

/*
 * Reduce to full NORMAL FORM (not just WHNF)
 * After WHNF, recursively normalize the captured arguments of PAPs
 * 
 * ITERATIVE VERSION using explicit dynamically-growable work stack
 * to avoid C stack overflow on deeply nested terms.
 */

typedef enum {
    WORK_NORMALIZE,     /* normalize closure, result goes to 'result' */
    WORK_S1_DONE,       /* S1 child done, rebuild if changed */
    WORK_S2_X_DONE,     /* S2 first child done, continue to y */
    WORK_S2_Y_DONE,     /* S2 both children done, rebuild if changed */
    WORK_K1_DONE,       /* K1 child done, rebuild if changed */
} WorkType;

typedef struct {
    WorkType type;
    Closure *closure;      /* closure being processed */
    Closure *saved_x;      /* for S2: save normalized x while processing y */
} WorkItem;

typedef struct WorkStack {
    WorkItem *items;
    size_t sp;       /* stack pointer (next free slot) */
    size_t cap;      /* capacity */
} WorkStack;

static void work_stack_init(WorkStack *ws) {
    ws->cap = 4096;
    ws->items = malloc(ws->cap * sizeof(WorkItem));
    ws->sp = 0;
}

static void work_stack_free(WorkStack *ws) {
    free(ws->items);
    ws->items = NULL;
    ws->sp = ws->cap = 0;
}

static void work_stack_push(WorkStack *ws, WorkItem item) {
    if (ws->sp >= ws->cap) {
        ws->cap *= 2;
        ws->items = realloc(ws->items, ws->cap * sizeof(WorkItem));
        if (!ws->items) {
            fprintf(stderr, "STG: work stack realloc failed\n");
            exit(1);
        }
    }
    ws->items[ws->sp++] = item;
}

static Closure *stg_normalize(STG *stg, Closure *c) {
    WorkStack ws;
    work_stack_init(&ws);
    stg->ws_root = &ws;  /* pending items are GC roots */
    
    Closure *result = NULL;
    
    /* Computed goto jump table - gcc/clang extension */
    static const void *dispatch[] = {
        &&do_normalize,
        &&do_s1_done,
        &&do_s2_x_done,
        &&do_s2_y_done,
        &&do_k1_done,
    };
    
    #define DISPATCH() do { \
        if (ws.sp == 0) goto done; \
        item = ws.items[--ws.sp]; \
        goto *dispatch[item.type]; \
    } while (0)
    
    WorkItem item;
    work_stack_push(&ws, (WorkItem){WORK_NORMALIZE, c, NULL});
    DISPATCH();

do_normalize: {
    Closure *cur = stg_enter(stg, item.closure);
    
    if (cur->entry == entry_S || cur->entry == entry_K || cur->entry == entry_I) {
        result = cur;
        DISPATCH();
    }
    if (cur->entry == entry_S1) {
        work_stack_push(&ws, (WorkItem){WORK_S1_DONE, cur, NULL});
        work_stack_push(&ws, (WorkItem){WORK_NORMALIZE, cur->payload.s1.x, NULL});
        DISPATCH();
    }
    if (cur->entry == entry_S2) {
        work_stack_push(&ws, (WorkItem){WORK_S2_Y_DONE, cur, NULL});
        work_stack_push(&ws, (WorkItem){WORK_S2_X_DONE, cur, NULL});
        work_stack_push(&ws, (WorkItem){WORK_NORMALIZE, cur->payload.s2.x, NULL});
        DISPATCH();
    }
    if (cur->entry == entry_K1) {
        work_stack_push(&ws, (WorkItem){WORK_K1_DONE, cur, NULL});
        work_stack_push(&ws, (WorkItem){WORK_NORMALIZE, cur->payload.k1.x, NULL});
        DISPATCH();
    }
    if (cur->entry == entry_AP) {
        stg_push(stg, cur->payload.ap.arg);
        work_stack_push(&ws, (WorkItem){WORK_NORMALIZE, cur->payload.ap.f, NULL});
        DISPATCH();
    }
    if (cur->entry == entry_IND) {
        work_stack_push(&ws, (WorkItem){WORK_NORMALIZE, cur->payload.ind.target, NULL});
        DISPATCH();
    }
    result = cur;
    DISPATCH();
}

do_s1_done: {
    Closure *cur = item.closure;
    Closure *x = result;
    stg->extra_roots[0] = cur;
    stg->extra_roots[1] = x;
    stg_reserve(stg, 2);
    cur = stg->extra_roots[0];
    x = stg->extra_roots[1];
    stg->extra_roots[0] = stg->extra_roots[1] = NULL;
    if (x != cur->payload.s1.x) {
        Closure *new_c = stg_alloc(stg, 2);
        new_c->entry = entry_S1;
        new_c->payload.s1.x = x;
        result = new_c;
    } else {
        result = cur;
    }
    DISPATCH();
}

do_s2_x_done: {
    Closure *cur = item.closure;
    ws.items[ws.sp - 1].saved_x = result;
    work_stack_push(&ws, (WorkItem){WORK_NORMALIZE, cur->payload.s2.y, NULL});
    DISPATCH();
}

do_s2_y_done: {
    Closure *cur = item.closure;
    Closure *x = item.saved_x;
    Closure *y = result;
    stg->extra_roots[0] = cur;
    stg->extra_roots[1] = x;
    stg->extra_roots[2] = y;
    stg_reserve(stg, 3);
    cur = stg->extra_roots[0];
    x = stg->extra_roots[1];
    y = stg->extra_roots[2];
    stg->extra_roots[0] = stg->extra_roots[1] = stg->extra_roots[2] = NULL;
    if (x != cur->payload.s2.x || y != cur->payload.s2.y) {
        Closure *new_c = stg_alloc(stg, 3);
        new_c->entry = entry_S2;
        new_c->payload.s2.x = x;
        new_c->payload.s2.y = y;
        result = new_c;
    } else {
        result = cur;
    }
    DISPATCH();
}

do_k1_done: {
    Closure *cur = item.closure;
    Closure *x = result;
    stg->extra_roots[0] = cur;
    stg->extra_roots[1] = x;
    stg_reserve(stg, 2);
    cur = stg->extra_roots[0];
    x = stg->extra_roots[1];
    stg->extra_roots[0] = stg->extra_roots[1] = NULL;
    if (x != cur->payload.k1.x) {
        Closure *new_c = stg_alloc(stg, 2);
        new_c->entry = entry_K1;
        new_c->payload.k1.x = x;
        result = new_c;
    } else {
        result = cur;
    }
    DISPATCH();
}

done:
    #undef DISPATCH
    stg->ws_root = NULL;
    work_stack_free(&ws);
    return result;
}

/*
 * Convert SKITerm to STG closure
 * ITERATIVE VERSION using explicit dynamically-growable stack
 */

typedef enum {
    CONV_VISIT,        /* visit this term */
    CONV_APP_RIGHT,    /* left child done, do right */
    CONV_APP_BUILD,    /* both children done, build AP */
} ConvType;

typedef struct {
    ConvType type;
    SKITerm *term;
    Closure *left_result;
} ConvItem;

typedef struct ConvStack {
    ConvItem *items;
    size_t sp;
    size_t cap;
} ConvStack;

static void conv_stack_init(ConvStack *cs) {
    cs->cap = 4096;
    cs->items = malloc(cs->cap * sizeof(ConvItem));
    cs->sp = 0;
}

static void conv_stack_free(ConvStack *cs) {
    free(cs->items);
    cs->items = NULL;
    cs->sp = cs->cap = 0;
}

static void conv_stack_push(ConvStack *cs, ConvItem item) {
    if (cs->sp >= cs->cap) {
        cs->cap *= 2;
        cs->items = realloc(cs->items, cs->cap * sizeof(ConvItem));
        if (!cs->items) {
            fprintf(stderr, "STG: conv stack realloc failed\n");
            exit(1);
        }
    }
    cs->items[cs->sp++] = item;
}

static ConvItem conv_stack_pop(ConvStack *cs) {
    return cs->items[--cs->sp];
}

static Closure *term_to_stg(STG *stg, SKITerm *t) {
    ConvStack cs;
    conv_stack_init(&cs);
    stg->cs_root = &cs;  /* pending left_results are GC roots */
    
    Closure *result = NULL;
    
    conv_stack_push(&cs, (ConvItem){CONV_VISIT, t, NULL});
    
    while (cs.sp > 0) {
        ConvItem item = conv_stack_pop(&cs);
        
        switch (item.type) {
        case CONV_VISIT:
            switch (item.term->tag) {
            case TERM_S:
                result = stg->prim_S;
                break;
            case TERM_K:
                result = stg->prim_K;
                break;
            case TERM_I:
                result = stg->prim_I;
                break;
            case TERM_APP:
                conv_stack_push(&cs, (ConvItem){CONV_APP_BUILD, item.term, NULL});
                conv_stack_push(&cs, (ConvItem){CONV_APP_RIGHT, item.term, NULL});
                conv_stack_push(&cs, (ConvItem){CONV_VISIT, item.term->app.left, NULL});
                break;
            }
            break;
            
        case CONV_APP_RIGHT:
            /* left is done (in result), save it and do right */
            cs.items[cs.sp - 1].left_result = result;
            conv_stack_push(&cs, (ConvItem){CONV_VISIT, item.term->app.right, NULL});
            break;
            
        case CONV_APP_BUILD: {
            Closure *f = item.left_result;
            Closure *arg = result;
            stg->extra_roots[0] = f;
            stg->extra_roots[1] = arg;
            stg_reserve(stg, 3);
            f = stg->extra_roots[0];
            arg = stg->extra_roots[1];
            stg->extra_roots[0] = stg->extra_roots[1] = NULL;
            Closure *ap = stg_alloc(stg, 3);
            ap->entry = entry_AP;
            ap->payload.ap.f = f;
            ap->payload.ap.arg = arg;
            result = ap;
            break;
        }
        }
    }
    
    stg->cs_root = NULL;
    conv_stack_free(&cs);
    return result;
}

/*
 * Convert STG closure back to SKITerm
 * ITERATIVE VERSION using explicit dynamically-growable stack
 */

typedef enum {
    BACK_VISIT,
    BACK_S1_DONE,
    BACK_S2_X_DONE,
    BACK_S2_BUILD,
    BACK_K1_DONE,
    BACK_AP_LEFT_DONE,
    BACK_AP_BUILD,
} BackType;

typedef struct {
    BackType type;
    Closure *closure;
    SKITerm *left_result;
} BackItem;

typedef struct {
    BackItem *items;
    size_t sp;
    size_t cap;
} BackStack;

static void back_stack_init(BackStack *bs) {
    bs->cap = 4096;
    bs->items = malloc(bs->cap * sizeof(BackItem));
    bs->sp = 0;
}

static void back_stack_free(BackStack *bs) {
    free(bs->items);
    bs->items = NULL;
    bs->sp = bs->cap = 0;
}

static void back_stack_push(BackStack *bs, BackItem item) {
    if (bs->sp >= bs->cap) {
        bs->cap *= 2;
        bs->items = realloc(bs->items, bs->cap * sizeof(BackItem));
        if (!bs->items) {
            fprintf(stderr, "STG: back stack realloc failed\n");
            exit(1);
        }
    }
    bs->items[bs->sp++] = item;
}

static BackItem back_stack_pop(BackStack *bs) {
    return bs->items[--bs->sp];
}

static SKITerm *stg_to_term(SKIPool *pool, Closure *c) {
    BackStack bs;
    back_stack_init(&bs);
    
    SKITerm *result = NULL;
    
    back_stack_push(&bs, (BackItem){BACK_VISIT, c, NULL});
    
    while (bs.sp > 0) {
        BackItem item = back_stack_pop(&bs);
        
        switch (item.type) {
        case BACK_VISIT: {
            Closure *cur = item.closure;
            
            /* Follow indirections */
            while (cur->entry == entry_IND) {
                cur = cur->payload.ind.target;
            }
            
            if (cur->entry == entry_S) {
                result = ski_s(pool);
            }
            else if (cur->entry == entry_K) {
                result = ski_k(pool);
            }
            else if (cur->entry == entry_I) {
                result = ski_i(pool);
            }
            else if (cur->entry == entry_S1) {
                back_stack_push(&bs, (BackItem){BACK_S1_DONE, cur, NULL});
                back_stack_push(&bs, (BackItem){BACK_VISIT, cur->payload.s1.x, NULL});
            }
            else if (cur->entry == entry_S2) {
                back_stack_push(&bs, (BackItem){BACK_S2_BUILD, cur, NULL});
                back_stack_push(&bs, (BackItem){BACK_S2_X_DONE, cur, NULL});
                back_stack_push(&bs, (BackItem){BACK_VISIT, cur->payload.s2.x, NULL});
            }
            else if (cur->entry == entry_K1) {
                back_stack_push(&bs, (BackItem){BACK_K1_DONE, cur, NULL});
                back_stack_push(&bs, (BackItem){BACK_VISIT, cur->payload.k1.x, NULL});
            }
            else if (cur->entry == entry_AP) {
                back_stack_push(&bs, (BackItem){BACK_AP_BUILD, cur, NULL});
                back_stack_push(&bs, (BackItem){BACK_AP_LEFT_DONE, cur, NULL});
                back_stack_push(&bs, (BackItem){BACK_VISIT, cur->payload.ap.f, NULL});
            }
            else {
                result = ski_i(pool);  /* fallback */
            }
            break;
        }
        
        case BACK_S1_DONE: {
            SKITerm *x = result;
            result = ski_app(pool, ski_s(pool), x);
            break;
        }
        
        case BACK_S2_X_DONE: {
            /* x done, save and do y */
            bs.items[bs.sp - 1].left_result = result;
            back_stack_push(&bs, (BackItem){BACK_VISIT, item.closure->payload.s2.y, NULL});
            break;
        }
        
        case BACK_S2_BUILD: {
            SKITerm *x = item.left_result;
            SKITerm *y = result;
            result = ski_app(pool, ski_app(pool, ski_s(pool), x), y);
            break;
        }
        
        case BACK_K1_DONE: {
            SKITerm *x = result;
            result = ski_app(pool, ski_k(pool), x);
            break;
        }
        
        case BACK_AP_LEFT_DONE: {
            /* f done, save and do arg */
            bs.items[bs.sp - 1].left_result = result;
            back_stack_push(&bs, (BackItem){BACK_VISIT, item.closure->payload.ap.arg, NULL});
            break;
        }
        
        case BACK_AP_BUILD: {
            SKITerm *f = item.left_result;
            SKITerm *arg = result;
            result = ski_app(pool, f, arg);
            break;
        }
        }
    }
    
    back_stack_free(&bs);
    return result;
}

/* ========================================================================
 * CHENEY COPYING GARBAGE COLLECTOR
 * 
 * Two semi-spaces: when one fills, copy live data to the other.
 * Uses forwarding pointers to preserve sharing.
 * ======================================================================== */

/*
 * Check if pointer is in the from-space
 */
static int in_from_space(STG *stg, Closure *p) {
    Closure *from_base = stg->space[stg->active_space];
    Closure *from_end = (Closure*)((char*)from_base + stg->heap_size);
    return p >= from_base && p < from_end;
}

/*
 * Copy a single closure to to-space, return new location
 * If already copied (forwarding pointer), return the forward address
 */
static Closure *gc_copy(STG *stg, Closure *from, Closure **to_hp) {
    if (!from) return NULL;
    
    /* Primitives are allocated at fixed locations at start - don't copy */
    if (from == stg->prim_S || from == stg->prim_K || from == stg->prim_I) {
        return from;
    }
    
    /* If not in from-space, don't copy (shouldn't happen) */
    if (!in_from_space(stg, from)) {
        return from;
    }
    
    /* Check for forwarding pointer */
    if (from->entry == entry_FWD) {
        return from->payload.ind.target;
    }
    
    /* Copy the closure */
    int size = closure_size(from);
    Closure *to = *to_hp;
    memcpy(to, from, size * WORD);
    *to_hp = (Closure*)((char*)*to_hp + size * WORD);
    stg->bytes_copied += size * WORD;
    
    /* Install forwarding pointer in from-space */
    from->entry = entry_FWD;
    from->payload.ind.target = to;
    
    return to;
}

/*
 * Scavenge a closure - update its pointers to point to to-space
 */
static void gc_scavenge(STG *stg, Closure *c, Closure **to_hp) {
    if (c->entry == entry_S1) {
        c->payload.s1.x = gc_copy(stg, c->payload.s1.x, to_hp);
    } else if (c->entry == entry_S2) {
        c->payload.s2.x = gc_copy(stg, c->payload.s2.x, to_hp);
        c->payload.s2.y = gc_copy(stg, c->payload.s2.y, to_hp);
    } else if (c->entry == entry_K1) {
        c->payload.k1.x = gc_copy(stg, c->payload.k1.x, to_hp);
    } else if (c->entry == entry_AP) {
        c->payload.ap.f = gc_copy(stg, c->payload.ap.f, to_hp);
        c->payload.ap.arg = gc_copy(stg, c->payload.ap.arg, to_hp);
    } else if (c->entry == entry_IND) {
        c->payload.ind.target = gc_copy(stg, c->payload.ind.target, to_hp);
    }
    /* S, K, I have no pointers to scavenge */
}

/*
 * Cheney's algorithm - the main GC loop
 */
static void stg_gc(STG *stg) {
    stg->gc_count++;
    stg->bytes_copied = 0;
    
    int from_space = stg->active_space;
    int to_space = 1 - from_space;
    
    Closure *to_base = stg->space[to_space];
    Closure *to_hp = to_base;  /* allocation pointer in to-space */
    Closure *scan = to_base;    /* scan pointer for scavenging */
    
    /* First, copy the primitives to the new space */
    /* (They're singletons, need to be in both spaces) */
    Closure *new_S = to_hp;
    new_S->entry = entry_S;
    to_hp = (Closure*)((char*)to_hp + WORD);
    
    Closure *new_K = to_hp;
    new_K->entry = entry_K;
    to_hp = (Closure*)((char*)to_hp + WORD);
    
    Closure *new_I = to_hp;
    new_I->entry = entry_I;
    to_hp = (Closure*)((char*)to_hp + WORD);
    
    scan = to_hp;  /* don't scavenge primitives */
    
    /* Copy roots: current node being evaluated */
    if (stg->current_node) {
        stg->current_node = gc_copy(stg, stg->current_node, &to_hp);
    }
    
    /* Copy roots: argument stack */
    for (Closure **p = stg->sp; p < stg->stack_base; p++) {
        *p = gc_copy(stg, *p, &to_hp);
    }
    
    /* Copy roots: update stack thunks */
    for (int i = 0; i < stg->update_sp; i++) {
        stg->update_stack[i].thunk = gc_copy(stg, stg->update_stack[i].thunk, &to_hp);
    }
    
    /* Copy roots: C-held temporaries stashed around a stg_reserve() */
    for (int i = 0; i < 4; i++) {
        if (stg->extra_roots[i]) {
            stg->extra_roots[i] = gc_copy(stg, stg->extra_roots[i], &to_hp);
        }
    }
    
    /* Copy roots: pending normalizer work items */
    if (stg->ws_root) {
        for (size_t i = 0; i < stg->ws_root->sp; i++) {
            WorkItem *w = &stg->ws_root->items[i];
            w->closure = gc_copy(stg, w->closure, &to_hp);
            w->saved_x = gc_copy(stg, w->saved_x, &to_hp);
        }
    }
    
    /* Copy roots: pending term_to_stg conversion items */
    if (stg->cs_root) {
        for (size_t i = 0; i < stg->cs_root->sp; i++) {
            ConvItem *ci = &stg->cs_root->items[i];
            ci->left_result = gc_copy(stg, ci->left_result, &to_hp);
        }
    }
    
    /* Cheney loop: scan copied closures and copy their children */
    while (scan < to_hp) {
        gc_scavenge(stg, scan, &to_hp);
        int size = closure_size(scan);
        scan = (Closure*)((char*)scan + size * WORD);
    }
    
    /* Update primitives */
    stg->prim_S = new_S;
    stg->prim_K = new_K;
    stg->prim_I = new_I;
    
    /* Swap spaces */
    stg->active_space = to_space;
    stg->hp = to_hp;
    stg->heap_end = (Closure*)((char*)to_base + stg->heap_size);
    
#if 0
    size_t used = (char*)to_hp - (char*)to_base;
    fprintf(stderr, "GC #%llu: copied %llu bytes, %zu bytes used\n", 
            stg->gc_count, stg->bytes_copied, used);
#endif
}

/*
 * Initialize STG machine with two semi-spaces
 */
static void stg_init(void) {
    if (g_stg) return;
    
    g_stg = malloc(sizeof(STG));
    memset(g_stg, 0, sizeof(STG));
    
    g_stg->heap_size = HEAP_SIZE;
    g_stg->space[0] = malloc(HEAP_SIZE);
    g_stg->space[1] = malloc(HEAP_SIZE);
    g_stg->active_space = 0;
    g_stg->hp = g_stg->space[0];
    g_stg->heap_end = (Closure*)((char*)g_stg->space[0] + HEAP_SIZE);
    
    g_stg->stack = malloc(STACK_SIZE);
    g_stg->stack_base = (Closure**)((char*)g_stg->stack + STACK_SIZE);
    g_stg->sp = g_stg->stack_base;
    
    g_stg->update_size = 1024;
    g_stg->update_stack = malloc(g_stg->update_size * sizeof(g_stg->update_stack[0]));
    g_stg->update_sp = 0;
    
    /* Pre-build primitive closures (singletons) */
    g_stg->prim_S = stg_alloc(g_stg, 1);
    g_stg->prim_S->entry = entry_S;
    
    g_stg->prim_K = stg_alloc(g_stg, 1);
    g_stg->prim_K->entry = entry_K;
    
    g_stg->prim_I = stg_alloc(g_stg, 1);
    g_stg->prim_I->entry = entry_I;
    
    g_stg->gc_count = 0;
}

/*
 * Reset STG machine for new evaluation
 */
static void stg_reset(void) {
    /* Reset to space 0, preserving primitives at start */
    g_stg->active_space = 0;
    g_stg->hp = (Closure*)((char*)g_stg->space[0] + 3 * WORD);
    g_stg->heap_end = (Closure*)((char*)g_stg->space[0] + g_stg->heap_size);
    g_stg->sp = g_stg->stack_base;
    g_stg->update_sp = 0;
    g_stg->current_node = NULL;
    for (int i = 0; i < 4; i++) g_stg->extra_roots[i] = NULL;
    g_stg->ws_root = NULL;
    g_stg->cs_root = NULL;
    g_stg->next = NULL;
    g_stg->whnf = 0;
    g_stg->steps = 0;
    g_stg->max_steps = 0;
    
    /* Re-establish primitives at start of space 0 */
    g_stg->prim_S = g_stg->space[0];
    g_stg->prim_S->entry = entry_S;
    g_stg->prim_K = (Closure*)((char*)g_stg->space[0] + WORD);
    g_stg->prim_K->entry = entry_K;
    g_stg->prim_I = (Closure*)((char*)g_stg->space[0] + 2 * WORD);
    g_stg->prim_I->entry = entry_I;
}

/*
 * Public API
 */

SKITerm *stg_reduce(SKIPool *pool, SKITerm *term, i64 *steps, int whnf) {
    stg_init();
    stg_reset();
    
    /* If *steps is nonzero, use it as a bound */
    g_stg->max_steps = *steps;
    g_stg->whnf = whnf;
    
    int status = setjmp(g_stg->exit_jmp);
    if (status == 1) {
        /* Error occurred */
        *steps = -1;
        return ski_i(pool);
    }
    if (status == 2) {
        /* Step limit exceeded - return current steps */
        *steps = g_stg->steps;
        return ski_i(pool);
    }
    
    /* Convert to STG representation */
    Closure *c = term_to_stg(g_stg, term);
    
    /* Reduce: full normal form (args of PAPs normalized recursively),
     * or weak head normal form only */
    Closure *result = g_stg->whnf ? stg_enter(g_stg, c) : stg_normalize(g_stg, c);
    
    /* Convert back */
    SKITerm *result_term = stg_to_term(pool, result);
    
    *steps = g_stg->steps;
    return result_term;
}

/* ========================================================================
 * Lazy-K / WHNF stream I/O driver (see io.h)
 * ======================================================================== */

static Closure *io_ap(STG *stg, Closure *f, Closure *x) {
    Closure *c = stg_alloc(stg, 3);
    c->entry = entry_AP;
    c->payload.ap.f = f;
    c->payload.ap.arg = x;
    return c;
}

/* cons x y = S (S I (K x)) (K y): five cells; `si` is the shared (S I).
 * *ky_out receives the (K y) cell so a cycle can be closed afterwards. */
static Closure *io_cons(STG *stg, Closure *si, Closure *x, Closure *y, Closure **ky_out) {
    Closure *kx = io_ap(stg, stg->prim_K, x);
    Closure *a  = io_ap(stg, si, kx);
    Closure *b  = io_ap(stg, stg->prim_S, a);
    Closure *ky = io_ap(stg, stg->prim_K, y);
    *ky_out = ky;
    return io_ap(stg, b, ky);
}

int stg_run_io(SKIPool *pool, SKITerm *prog, const u8 *data, size_t len) {
    (void)pool;
    stg_init();
    stg_reset();
    STG *stg = g_stg;
    
    if (setjmp(stg->exit_jmp)) {
        io_flush();
        return 1;
    }
    
    Closure *P = term_to_stg(stg, prog);
    
    /* The whole input stream is built inside one reserved block, so no
     * collection can run while C locals point into it. */
    size_t words = 2 + 12 + 256 * 3 + 3 + 15 * len + 15 + 3;
    if (words + 64 > stg->heap_size / WORD) {
        fprintf(stderr, "io: input too large for the STG heap (%zu bytes)\n", len);
        return 1;
    }
    stg->extra_roots[0] = P;
    stg_reserve(stg, (int)words);
    P = stg->extra_roots[0];
    stg->extra_roots[0] = NULL;
    
    /* Church numerals 0..256 as one shared chain:
     *   num[0] = K I,  num[k] = succ num[k-1],  succ = S (S (K S) K) */
    Closure *ki = stg_alloc(stg, 2);
    ki->entry = entry_K1;
    ki->payload.k1.x = stg->prim_I;
    Closure *succ = io_ap(stg, stg->prim_S,
                          io_ap(stg, io_ap(stg, stg->prim_S, io_ap(stg, stg->prim_K, stg->prim_S)),
                                stg->prim_K));
    Closure *num[257];
    num[0] = ki;
    for (int k = 1; k <= 256; k++) num[k] = io_ap(stg, succ, num[k - 1]);
    
    /* EOF: an infinite stream of 256, as a cycle */
    Closure *si = io_ap(stg, stg->prim_S, stg->prim_I);
    Closure *ky;
    Closure *eof = io_cons(stg, si, num[256], NULL, &ky);
    ky->payload.ap.arg = eof;
    
    /* The data, back to front */
    Closure *s = eof;
    for (size_t i = len; i > 0; i--) s = io_cons(stg, si, num[data[i - 1]], s, &ky);
    
    Closure *o = io_ap(stg, P, s);
    
    for (;;) {
        Closure *v = stg_enter(stg, o);                        /* the output cell (WHNF) */
        stg->extra_roots[0] = v;
        stg_reserve(stg, 3);
        v = stg->extra_roots[0];
        Closure *h = stg_enter(stg, io_ap(stg, v, stg->prim_K));   /* head = v K */
        stg->extra_roots[1] = h;
        stg_reserve(stg, 6);
        h = stg->extra_roots[1];
        stg->extra_roots[1] = NULL;
        Closure *t = stg_enter(stg, io_ap(stg, io_ap(stg, h, stg->prim_K), stg->prim_S));   /* h K S */
        long n = 0;
        while (t->entry == entry_K1) {                          /* K1[u]: one more, unfold u */
            n++;
            t = stg_enter(stg, t->payload.k1.x);
        }
        v = stg->extra_roots[0];
        if (t->entry != entry_S) {
            io_flush();
            fprintf(stderr, "io: output element is not a numeral\n");
            return 1;
        }
        if (n >= 256) {
            io_flush();
            return (int)(n - 256);
        }
        io_put_byte((int)n);
        stg_reserve(stg, 5);
        v = stg->extra_roots[0];
        stg->extra_roots[0] = NULL;
        Closure *kI = stg_alloc(stg, 2);                        /* K I */
        kI->entry = entry_K1;
        kI->payload.k1.x = stg->prim_I;
        o = io_ap(stg, v, kI);                                  /* tail = v (K I) */
    }
}
