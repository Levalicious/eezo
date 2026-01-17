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
    
    /* Update frames: when we enter a thunk, push its address */
    /* so we can overwrite it when we get the result */
    struct {
        Closure *thunk;
        Closure **saved_sp;
    } *update_stack;
    int update_sp;
    int update_size;
    
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
 * Pop from argument stack
 */
static Closure *stg_pop(STG *stg) {
    if (stg->sp >= stg->stack_base) {
        return NULL;  /* stack empty */
    }
    return *stg->sp++;
}

/*
 * Number of args on stack
 */
static int stg_stack_size(STG *stg) {
    return (int)(stg->stack_base - stg->sp);
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
            Closure *x = stg_pop(stg);
            Closure *s1 = stg_alloc(stg, 2);
            s1->entry = entry_S1;
            s1->payload.s1.x = x;
            return s1;
        } else { /* n == 2 */
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
    return x->entry(stg, x);
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
    Closure *x = self->payload.s1.x;
    Closure *y = stg_pop(stg);
    Closure *z = stg_pop(stg);
    
    Closure *yz = stg_alloc(stg, 3);
    yz->entry = entry_AP;
    yz->payload.ap.f = y;
    yz->payload.ap.arg = z;
    
    stg_push(stg, yz);
    stg_push(stg, z);
    
    return x->entry(stg, x);
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
    Closure *x = self->payload.s2.x;
    Closure *y = self->payload.s2.y;
    Closure *z = stg_pop(stg);
    
    Closure *yz = stg_alloc(stg, 3);
    yz->entry = entry_AP;
    yz->payload.ap.f = y;
    yz->payload.ap.arg = z;
    
    stg_push(stg, yz);
    stg_push(stg, z);
    
    return x->entry(stg, x);
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
    
    return x->entry(stg, x);
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
    
    return x->entry(stg, x);
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
    return x->entry(stg, x);
}

/*
 * Application thunk entry code
 * (f arg) → push arg, enter f
 */
static Closure *entry_AP(STG *stg, Closure *self) {
    Closure *f = self->payload.ap.f;
    Closure *arg = self->payload.ap.arg;
    
    stg_push(stg, arg);
    return f->entry(stg, f);
}

/*
 * Indirection entry code
 * Follows the indirection chain
 */
static Closure *entry_IND(STG *stg, Closure *self) {
    Closure *target = self->payload.ind.target;
    return target->entry(stg, target);
}

/*
 * Enter a closure - THE ONLY DISPATCH POINT
 * This is now just a single indirect call, not a switch!
 */
static Closure *stg_enter(STG *stg, Closure *c) {
    stg->current_node = c;  /* Mark as GC root */
    Closure *result = c->entry(stg, c);
    stg->current_node = result;  /* Update root after reduction */
    return result;
}

/*
 * Reduce to full HNF (not just WHNF)
 * After WHNF, recursively reduce arguments
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

typedef struct {
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

typedef struct {
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
            Closure *ap = stg_alloc(stg, 3);
            ap->entry = entry_AP;
            ap->payload.ap.f = f;
            ap->payload.ap.arg = arg;
            result = ap;
            break;
        }
        }
    }
    
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

SKITerm *stg_reduce(SKIPool *pool, SKITerm *term, i64 *steps) {
    stg_init();
    stg_reset();
    
    /* If *steps is nonzero, use it as a bound */
    g_stg->max_steps = *steps;
    
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
    
    /* Reduce to HNF */
    Closure *result = stg_normalize(g_stg, c);
    
    /* Convert back */
    SKITerm *result_term = stg_to_term(pool, result);
    
    *steps = g_stg->steps;
    return result_term;
}
