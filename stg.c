#include <libeezo/mem.h>
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

/* The machine's first sizes, not its limits: the semi-spaces grow after a collection that leaves them more than half
   full, the argument stack grows when it fills, and the only limit is the memory layer's (mem.h) */
#define HEAP_SIZE   (16 * 1024 * 1024)  /* each semi-space, at start */
#define STACK_SIZE  (256 * 1024)        /* the argument stack, at start */
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
        struct { struct Closure *x; } s1;           /* S x; the layout of every one-argument PAP: S1 K1 B1 C1 T1 R1 (and PRIM1's x) */
        struct { struct Closure *x, *y; } s2;       /* S x y; the layout of every two-argument PAP: S2 B2 C2 R2 */
        struct { struct Closure *x; } k1;           /* K x */
        struct { struct Closure *f, *arg; } ap;     /* f @ arg */
        struct { struct Closure *target; } ind;     /* -> target (also used as forwarding ptr) */
        u64 word;                                   /* WORD: the machine word (not a pointer) */
        struct { u64 op; } prim;                    /* PRIM singleton: its PrimOp */
        struct { struct Closure *x; u64 op; } prim1; /* PRIM1: op applied to x (x first, so the one-argument PAP layout holds) */
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
    size_t heap_size;     /* size of each semi-space (they grow together: stg_make_room) */
    Closure *gc_to;       /* during a collection: the space it copies into */
    
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
    
    /* Pre-built primitive closures (shared singletons): S K I B C T R and one per word primitive */
    Closure *prim_S;
    Closure *prim_K;
    Closure *prim_I;
    Closure *prim_B;
    Closure *prim_C;
    Closure *prim_T;
    Closure *prim_R;
    Closure *prim_op[PRIM_COUNT];
    
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
static Closure *entry_B(STG *stg, Closure *self);
static Closure *entry_B1(STG *stg, Closure *self);
static Closure *entry_B2(STG *stg, Closure *self);
static Closure *entry_C(STG *stg, Closure *self);
static Closure *entry_C1(STG *stg, Closure *self);
static Closure *entry_C2(STG *stg, Closure *self);
static Closure *entry_T(STG *stg, Closure *self);
static Closure *entry_T1(STG *stg, Closure *self);
static Closure *entry_R(STG *stg, Closure *self);
static Closure *entry_R1(STG *stg, Closure *self);
static Closure *entry_R2(STG *stg, Closure *self);
static Closure *entry_WORD(STG *stg, Closure *self);
static Closure *prim_step(STG *stg, u64 op, Closure *x, Closure *y);
static Closure *entry_PRIM(STG *stg, Closure *self);
static Closure *entry_PRIM1(STG *stg, Closure *self);

/* Kinds by shape: a leaf value (one word, or a word/primitive with its datum); a PAP with one captured argument
 * (x at payload word 1); a PAP with two (x, y at words 1, 2). */
static int is_leaf(Closure *c) {
    EntryCode e = c->entry;
    return e == entry_S || e == entry_K || e == entry_I || e == entry_B || e == entry_C || e == entry_T || e == entry_R ||
           e == entry_WORD || e == entry_PRIM;
}
static int pap1_kind(EntryCode e) {
    return e == entry_S1 || e == entry_K1 || e == entry_B1 || e == entry_C1 || e == entry_T1 || e == entry_R1 || e == entry_PRIM1;
}
static int pap2_kind(EntryCode e) {
    return e == entry_S2 || e == entry_B2 || e == entry_C2 || e == entry_R2;
}

/* The singletons live at the start of every semispace, in this order:
 * S K I B C T R (one word each), then the word primitives (two words each: entry, op). */
#define SINGLETON_WORDS (7 + 2 * PRIM_COUNT)
static void singletons_build(STG *stg, Closure *base) {
    char *p = (char*)base;
    Closure *c;
    c = (Closure*)p; c->entry = entry_S; stg->prim_S = c; p += WORD;
    c = (Closure*)p; c->entry = entry_K; stg->prim_K = c; p += WORD;
    c = (Closure*)p; c->entry = entry_I; stg->prim_I = c; p += WORD;
    c = (Closure*)p; c->entry = entry_B; stg->prim_B = c; p += WORD;
    c = (Closure*)p; c->entry = entry_C; stg->prim_C = c; p += WORD;
    c = (Closure*)p; c->entry = entry_T; stg->prim_T = c; p += WORD;
    c = (Closure*)p; c->entry = entry_R; stg->prim_R = c; p += WORD;
    for (int op = 0; op < PRIM_COUNT; op++) {
        c = (Closure*)p; c->entry = entry_PRIM; c->payload.prim.op = (u64)op; stg->prim_op[op] = c; p += 2 * WORD;
    }
}

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
    EntryCode e = c->entry;
    if (e == entry_S || e == entry_K || e == entry_I || e == entry_B || e == entry_C || e == entry_T || e == entry_R) {
        return 1;  /* just entry ptr */
    }
    if (pap1_kind(e) && e != entry_PRIM1) {
        return 2;  /* entry + 1 pointer */
    }
    if (e == entry_IND || e == entry_FWD || e == entry_WORD || e == entry_PRIM) {
        return 2;  /* entry + 1 pointer, or entry + datum */
    }
    if (pap2_kind(e) || e == entry_AP || e == entry_PRIM1) {
        return 3;  /* entry + 2 pointers, or entry + pointer + datum */
    }
    fprintf(stderr, "STG: closure of unknown kind\n");
    abort();
}

/*
 * Allocate on heap - triggers GC if needed
 */
static void stg_make_room(STG *stg, size_t need_bytes);
static Closure *stg_alloc(STG *stg, int words) {
    Closure *new_hp = (Closure*)((char*)stg->hp + words * WORD);
    if ((char*)new_hp >= (char*)stg->heap_end) {
        stg_gc(stg);                                  /* collect, then grow if the space is still too full */
        stg_make_room(stg, (size_t)words * WORD);
        new_hp = (Closure*)((char*)stg->hp + words * WORD);
    }
    Closure *p = stg->hp;
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
static void stg_reserve(STG *stg, size_t words) {
    if ((size_t)((char*)stg->heap_end - (char*)stg->hp) <= words * WORD) {
        stg_gc(stg);
        stg_make_room(stg, words * WORD);
    }
}

/*
 * Push to argument stack
 */
/* the argument stack full: twice the room, the contents moved to the new top (it grows down), and every pointer into
   it - sp, the update frames' barriers - moved with them (nothing else points into it) */
static void stg_grow_stack(STG *stg) {
    size_t used = (size_t)(stg->stack_base - stg->sp), cap = (size_t)(stg->stack_base - stg->stack), nc = cap * 2;
    Closure **ns = rmalloc(nc * sizeof(Closure*)), **nbase = ns + nc;
    memcpy(nbase - used, stg->sp, used * sizeof(Closure*));
    ptrdiff_t delta = nbase - stg->stack_base;
    for (int i = 0; i < stg->update_sp; i++) stg->update_stack[i].saved_sp += delta;
    free(stg->stack);
    stg->stack = ns; stg->stack_base = nbase; stg->sp = nbase - used;
}
static void stg_push(STG *stg, Closure *c) {
    if (stg->sp <= stg->stack) stg_grow_stack(stg);
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
        stg->update_stack = rrealloc(stg->update_stack,
                                    stg->update_size * sizeof(stg->update_stack[0]));
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

/* ------------------------------------------------------------------------
 * The extended leaves (2026-09-13): B C T R, words and their primitives.
 * The rules are those of term.h; here a word passes itself on by pushing
 * itself and entering its argument, and a primitive's continuations are
 * the closures B2[y, op] and PRIM1[x, op] built from the rules themselves.
 * ------------------------------------------------------------------------ */

static void count_step(STG *stg) {
    stg->steps++;
    if (stg->max_steps && stg->steps >= stg->max_steps) {
        longjmp(stg->exit_jmp, 2);
    }
}

/* Allocation helpers: the caller has reserved the words */
static Closure *pap1(STG *stg, EntryCode e, Closure *x) {
    Closure *c = stg_alloc(stg, 2);
    c->entry = e;
    c->payload.s1.x = x;
    return c;
}
static Closure *pap2(STG *stg, EntryCode e, Closure *x, Closure *y) {
    Closure *c = stg_alloc(stg, 3);
    c->entry = e;
    c->payload.s2.x = x;
    c->payload.s2.y = y;
    return c;
}
static Closure *mk_ap(STG *stg, Closure *f, Closure *arg) {
    Closure *c = stg_alloc(stg, 3);
    c->entry = entry_AP;
    c->payload.ap.f = f;
    c->payload.ap.arg = arg;
    return c;
}
static Closure *mk_word(STG *stg, u64 w) {
    Closure *c = stg_alloc(stg, 2);
    c->entry = entry_WORD;
    c->payload.word = w;
    return c;
}

static Closure *mk_prim1(STG *stg, u64 op, Closure *x) {
    Closure *c = stg_alloc(stg, 3);
    c->entry = entry_PRIM1;
    c->payload.prim1.x = x;
    c->payload.prim1.op = op;
    return c;
}

/*
 * B x y z -> x (y z)
 */
static Closure *entry_B(STG *stg, Closure *self) {
    (void)self;
    int n = stg_stack_size(stg);
    if (n == 0) return stg->prim_B;
    if (n == 1) {
        stg_reserve(stg, 2);
        Closure *x = stg_pop(stg);
        return pap1(stg, entry_B1, x);
    }
    if (n == 2) {
        stg_reserve(stg, 3);
        Closure *x = stg_pop(stg);
        Closure *y = stg_pop(stg);
        return pap2(stg, entry_B2, x, y);
    }
    count_step(stg);
    stg_reserve(stg, 3);
    Closure *x = stg_pop(stg);
    Closure *y = stg_pop(stg);
    Closure *z = stg_pop(stg);
    stg_push(stg, mk_ap(stg, y, z));
    return stg_tail(stg, x);
}

static Closure *entry_B1(STG *stg, Closure *self) {
    int n = stg_stack_size(stg);
    if (n == 0) return self;
    stg->current_node = self;
    stg_reserve(stg, 3);
    self = stg->current_node;
    Closure *x = self->payload.s1.x;
    if (n == 1) {
        Closure *y = stg_pop(stg);
        return pap2(stg, entry_B2, x, y);
    }
    count_step(stg);
    Closure *y = stg_pop(stg);
    Closure *z = stg_pop(stg);
    stg_push(stg, mk_ap(stg, y, z));
    return stg_tail(stg, x);
}

static Closure *entry_B2(STG *stg, Closure *self) {
    if (stg_stack_size(stg) < 1) return self;
    count_step(stg);
    stg->current_node = self;
    stg_reserve(stg, 3);
    self = stg->current_node;
    Closure *x = self->payload.s2.x;
    Closure *y = self->payload.s2.y;
    Closure *z = stg_pop(stg);
    stg_push(stg, mk_ap(stg, y, z));
    return stg_tail(stg, x);
}

/*
 * C x y z -> x z y   (no allocation: y then z go back on the stack)
 */
static Closure *entry_C(STG *stg, Closure *self) {
    (void)self;
    int n = stg_stack_size(stg);
    if (n == 0) return stg->prim_C;
    if (n == 1) {
        stg_reserve(stg, 2);
        Closure *x = stg_pop(stg);
        return pap1(stg, entry_C1, x);
    }
    if (n == 2) {
        stg_reserve(stg, 3);
        Closure *x = stg_pop(stg);
        Closure *y = stg_pop(stg);
        return pap2(stg, entry_C2, x, y);
    }
    count_step(stg);
    Closure *x = stg_pop(stg);
    Closure *y = stg_pop(stg);
    Closure *z = stg_pop(stg);
    stg_push(stg, y);
    stg_push(stg, z);
    return stg_tail(stg, x);
}

static Closure *entry_C1(STG *stg, Closure *self) {
    int n = stg_stack_size(stg);
    if (n == 0) return self;
    if (n == 1) {
        stg->current_node = self;
        stg_reserve(stg, 3);
        self = stg->current_node;
        Closure *y = stg_pop(stg);
        return pap2(stg, entry_C2, self->payload.s1.x, y);
    }
    count_step(stg);
    Closure *x = self->payload.s1.x;
    Closure *y = stg_pop(stg);
    Closure *z = stg_pop(stg);
    stg_push(stg, y);
    stg_push(stg, z);
    return stg_tail(stg, x);
}

static Closure *entry_C2(STG *stg, Closure *self) {
    if (stg_stack_size(stg) < 1) return self;
    count_step(stg);
    Closure *x = self->payload.s2.x;
    Closure *y = self->payload.s2.y;
    Closure *z = stg_pop(stg);
    stg_push(stg, y);
    stg_push(stg, z);
    return stg_tail(stg, x);
}

/*
 * T x f -> f x
 */
static Closure *entry_T(STG *stg, Closure *self) {
    (void)self;
    int n = stg_stack_size(stg);
    if (n == 0) return stg->prim_T;
    if (n == 1) {
        stg_reserve(stg, 2);
        Closure *x = stg_pop(stg);
        return pap1(stg, entry_T1, x);
    }
    count_step(stg);
    Closure *x = stg_pop(stg);
    Closure *f = stg_pop(stg);
    stg_push(stg, x);
    return stg_tail(stg, f);
}

static Closure *entry_T1(STG *stg, Closure *self) {
    if (stg_stack_size(stg) < 1) return self;
    count_step(stg);
    Closure *f = stg_pop(stg);
    stg_push(stg, self->payload.s1.x);
    return stg_tail(stg, f);
}

/*
 * R x y z -> y z x
 */
static Closure *entry_R(STG *stg, Closure *self) {
    (void)self;
    int n = stg_stack_size(stg);
    if (n == 0) return stg->prim_R;
    if (n == 1) {
        stg_reserve(stg, 2);
        Closure *x = stg_pop(stg);
        return pap1(stg, entry_R1, x);
    }
    if (n == 2) {
        stg_reserve(stg, 3);
        Closure *x = stg_pop(stg);
        Closure *y = stg_pop(stg);
        return pap2(stg, entry_R2, x, y);
    }
    count_step(stg);
    Closure *x = stg_pop(stg);
    Closure *y = stg_pop(stg);
    Closure *z = stg_pop(stg);
    stg_push(stg, x);
    stg_push(stg, z);
    return stg_tail(stg, y);
}

static Closure *entry_R1(STG *stg, Closure *self) {
    int n = stg_stack_size(stg);
    if (n == 0) return self;
    if (n == 1) {
        stg->current_node = self;
        stg_reserve(stg, 3);
        self = stg->current_node;
        Closure *y = stg_pop(stg);
        return pap2(stg, entry_R2, self->payload.s1.x, y);
    }
    count_step(stg);
    Closure *x = self->payload.s1.x;
    Closure *y = stg_pop(stg);
    Closure *z = stg_pop(stg);
    stg_push(stg, x);
    stg_push(stg, z);
    return stg_tail(stg, y);
}

static Closure *entry_R2(STG *stg, Closure *self) {
    if (stg_stack_size(stg) < 1) return self;
    count_step(stg);
    Closure *x = self->payload.s2.x;
    Closure *y = self->payload.s2.y;
    Closure *z = stg_pop(stg);
    stg_push(stg, x);
    stg_push(stg, z);
    return stg_tail(stg, y);
}

/*
 * #w f -> f #w
 */
static Closure *entry_WORD(STG *stg, Closure *self) {
    if (stg_stack_size(stg) < 1) return self;
    count_step(stg);
    Closure *f = stg_pop(stg);
    stg_push(stg, self);
    return stg_tail(stg, f);
}

/* The value of op #a #b: a word, a Scott boolean (K, K I) or a Scott pair C (T a) b; at most 9 words */
#define PRIM_VALUE_WORDS 9
static Closure *prim_pair(STG *stg, u64 a, u64 b) {
    Closure *t1 = pap1(stg, entry_T1, mk_word(stg, a));
    return pap2(stg, entry_C2, t1, mk_word(stg, b));
}
static Closure *prim_bool(STG *stg, int b) {
    return b ? stg->prim_K : pap1(stg, entry_K1, stg->prim_I);
}

static Closure *prim_value(STG *stg, u64 op, u64 a, u64 b) {
    switch ((PrimOp)op) {
    case PRIM_ADD: return mk_word(stg, a + b);
    case PRIM_SUB: return mk_word(stg, a - b);
    case PRIM_MUL: return mk_word(stg, a * b);
    case PRIM_AND: return mk_word(stg, a & b);
    case PRIM_OR:  return mk_word(stg, a | b);
    case PRIM_XOR: return mk_word(stg, a ^ b);
    case PRIM_SHL: return mk_word(stg, b >= 64 ? 0 : a << b);
    case PRIM_SHR: return mk_word(stg, b >= 64 ? 0 : a >> b);
    case PRIM_EQ:  return prim_bool(stg, a == b);
    case PRIM_LT:  return prim_bool(stg, a < b);
    case PRIM_ADDC: { u64 s = a + b; return prim_pair(stg, s, s < a); }
    case PRIM_SUBB: return prim_pair(stg, a - b, a < b);
    case PRIM_MULL: {
        unsigned __int128 m = (unsigned __int128)a * b;
        return prim_pair(stg, (u64)m, (u64)(m >> 64));
    }
    case PRIM_DIVMOD:
        if (b == 0) return prim_pair(stg, 0, a);
        return prim_pair(stg, a / b, a % b);
    default:
        fprintf(stderr, "STG: unknown primitive %llu\n", (unsigned long long)op);
        longjmp(stg->exit_jmp, 1);
    }
}

/*
 * op x y: the rules of term.h. PRIM_VALUE_WORDS reserved; x and y popped.
 */
static Closure *prim_step(STG *stg, u64 op, Closure *x, Closure *y) {
    Closure *xv = x;
    while (xv->entry == entry_IND) xv = xv->payload.ind.target;
    if (xv->entry != entry_WORD) {                       /* op x y -> x (B y op) */
        stg_push(stg, pap2(stg, entry_B2, y, stg->prim_op[op]));
        return stg_tail(stg, x);
    }
    Closure *yv = y;
    while (yv->entry == entry_IND) yv = yv->payload.ind.target;
    if (yv->entry != entry_WORD) {                       /* op x y -> y (op x) */
        stg_push(stg, mk_prim1(stg, op, xv));
        return stg_tail(stg, y);
    }
    return prim_value(stg, op, xv->payload.word, yv->payload.word);
}

static Closure *entry_PRIM(STG *stg, Closure *self) {
    int n = stg_stack_size(stg);
    if (n == 0) return self;
    u64 op = self->payload.prim.op;                      /* self is a singleton: it does not move */
    if (n == 1) {
        stg_reserve(stg, 3);
        Closure *x = stg_pop(stg);
        return mk_prim1(stg, op, x);
    }
    count_step(stg);
    stg_reserve(stg, PRIM_VALUE_WORDS);
    Closure *x = stg_pop(stg);
    Closure *y = stg_pop(stg);
    return prim_step(stg, op, x, y);
}

static Closure *entry_PRIM1(STG *stg, Closure *self) {
    if (stg_stack_size(stg) < 1) return self;
    count_step(stg);
    stg->current_node = self;
    stg_reserve(stg, PRIM_VALUE_WORDS);
    self = stg->current_node;
    Closure *y = stg_pop(stg);
    return prim_step(stg, self->payload.prim1.op, self->payload.prim1.x, y);
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
    WORK_P1_DONE,       /* a one-argument PAP's child done, rebuild if changed */
    WORK_P2_X_DONE,     /* a two-argument PAP's first child done, continue to y */
    WORK_P2_Y_DONE,     /* both children done, rebuild if changed */
} WorkType;

typedef struct {
    WorkType type;
    Closure *closure;      /* closure being processed */
    Closure *saved_x;      /* for two-argument PAPs: save normalized x while processing y */
} WorkItem;

typedef struct WorkStack { Stack s; } WorkStack;   /* a Stack of the memory layer (mem.h) */
static void work_stack_init(WorkStack *ws) { stack_init(&ws->s, sizeof(WorkItem)); }
static void work_stack_free(WorkStack *ws) { stack_drop(&ws->s); }
static void work_stack_push(WorkStack *ws, WorkItem item) { STACK_PUSH(&ws->s, WorkItem, item); }

static Closure *stg_normalize(STG *stg, Closure *c) {
    WorkStack ws;
    work_stack_init(&ws);
    stg->ws_root = &ws;  /* pending items are GC roots */
    
    Closure *result = NULL;
    
    /* Computed goto jump table - gcc/clang extension */
    static const void *dispatch[] = {
        &&do_normalize,
        &&do_p1_done,
        &&do_p2_x_done,
        &&do_p2_y_done,
    };
    
    #define DISPATCH() do { \
        if (ws.s.n == 0) goto done; \
        item = STACK_POP(&ws.s, WorkItem); \
        goto *dispatch[item.type]; \
    } while (0)
    
    WorkItem item;
    work_stack_push(&ws, (WorkItem){WORK_NORMALIZE, c, NULL});
    DISPATCH();

do_normalize: {
    Closure *cur = stg_enter(stg, item.closure);
    
    if (is_leaf(cur)) {
        result = cur;
        DISPATCH();
    }
    if (pap1_kind(cur->entry)) {
        work_stack_push(&ws, (WorkItem){WORK_P1_DONE, cur, NULL});
        work_stack_push(&ws, (WorkItem){WORK_NORMALIZE, cur->payload.s1.x, NULL});
        DISPATCH();
    }
    if (pap2_kind(cur->entry)) {
        work_stack_push(&ws, (WorkItem){WORK_P2_Y_DONE, cur, NULL});
        work_stack_push(&ws, (WorkItem){WORK_P2_X_DONE, cur, NULL});
        work_stack_push(&ws, (WorkItem){WORK_NORMALIZE, cur->payload.s2.x, NULL});
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

do_p1_done: {
    Closure *cur = item.closure;
    Closure *x = result;
    stg->extra_roots[0] = cur;
    stg->extra_roots[1] = x;
    stg_reserve(stg, 3);
    cur = stg->extra_roots[0];
    x = stg->extra_roots[1];
    stg->extra_roots[0] = stg->extra_roots[1] = NULL;
    if (x != cur->payload.s1.x) {
        int size = closure_size(cur);              /* the same kind (and datum, for PRIM1), with the normalized x */
        Closure *new_c = stg_alloc(stg, size);
        memcpy(new_c, cur, size * WORD);
        new_c->payload.s1.x = x;
        result = new_c;
    } else {
        result = cur;
    }
    DISPATCH();
}

do_p2_x_done: {
    Closure *cur = item.closure;
    STACK_TOP(&ws.s, WorkItem).saved_x = result;
    work_stack_push(&ws, (WorkItem){WORK_NORMALIZE, cur->payload.s2.y, NULL});
    DISPATCH();
}

do_p2_y_done: {
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
        result = pap2(stg, cur->entry, x, y);
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

typedef struct ConvStack { Stack s; } ConvStack;   /* a Stack of the memory layer (mem.h) */
static void conv_stack_init(ConvStack *cs) { stack_init(&cs->s, sizeof(ConvItem)); }
static void conv_stack_free(ConvStack *cs) { stack_drop(&cs->s); }
static void conv_stack_push(ConvStack *cs, ConvItem item) { STACK_PUSH(&cs->s, ConvItem, item); }
static ConvItem conv_stack_pop(ConvStack *cs) { return STACK_POP(&cs->s, ConvItem); }

static Closure *term_to_stg(STG *stg, SKITerm *t) {
    ConvStack cs;
    conv_stack_init(&cs);
    stg->cs_root = &cs;  /* pending left_results are GC roots */
    
    Closure *result = NULL;
    
    conv_stack_push(&cs, (ConvItem){CONV_VISIT, t, NULL});
    
    while (cs.s.n > 0) {
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
            case TERM_B:
                result = stg->prim_B;
                break;
            case TERM_C:
                result = stg->prim_C;
                break;
            case TERM_T:
                result = stg->prim_T;
                break;
            case TERM_R:
                result = stg->prim_R;
                break;
            case TERM_PRIM:
                result = stg->prim_op[item.term->op];
                break;
            case TERM_WORD:
                stg_reserve(stg, 2);
                result = mk_word(stg, item.term->word);
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
            STACK_TOP(&cs.s, ConvItem).left_result = result;
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
    BACK_P1_DONE,
    BACK_P2_X_DONE,
    BACK_P2_BUILD,
    BACK_AP_LEFT_DONE,
    BACK_AP_BUILD,
} BackType;

typedef struct {
    BackType type;
    Closure *closure;
    SKITerm *left_result;
} BackItem;

typedef struct { Stack s; } BackStack;   /* a Stack of the memory layer (mem.h) */
static void back_stack_init(BackStack *bs) { stack_init(&bs->s, sizeof(BackItem)); }
static void back_stack_free(BackStack *bs) { stack_drop(&bs->s); }
static void back_stack_push(BackStack *bs, BackItem item) { STACK_PUSH(&bs->s, BackItem, item); }
static BackItem back_stack_pop(BackStack *bs) { return STACK_POP(&bs->s, BackItem); }

/* A leaf closure, or the head of a PAP, as a term */
static SKITerm *head_term(SKIPool *pool, Closure *c) {
    EntryCode e = c->entry;
    if (e == entry_S || e == entry_S1 || e == entry_S2) return ski_s(pool);
    if (e == entry_K || e == entry_K1) return ski_k(pool);
    if (e == entry_I) return ski_i(pool);
    if (e == entry_B || e == entry_B1 || e == entry_B2) return ski_b(pool);
    if (e == entry_C || e == entry_C1 || e == entry_C2) return ski_c(pool);
    if (e == entry_T || e == entry_T1) return ski_t(pool);
    if (e == entry_R || e == entry_R1 || e == entry_R2) return ski_r(pool);
    if (e == entry_WORD) return ski_word(pool, c->payload.word);
    if (e == entry_PRIM) return ski_prim(pool, (PrimOp)c->payload.prim.op);
    if (e == entry_PRIM1) return ski_prim(pool, (PrimOp)c->payload.prim1.op);
    fprintf(stderr, "STG: cannot read back a closure of this kind\n");
    abort();
}

static SKITerm *stg_to_term(SKIPool *pool, Closure *c) {
    BackStack bs;
    back_stack_init(&bs);
    
    SKITerm *result = NULL;
    
    back_stack_push(&bs, (BackItem){BACK_VISIT, c, NULL});
    
    while (bs.s.n > 0) {
        BackItem item = back_stack_pop(&bs);
        
        switch (item.type) {
        case BACK_VISIT: {
            Closure *cur = item.closure;
            
            /* Follow indirections */
            while (cur->entry == entry_IND) {
                cur = cur->payload.ind.target;
            }
            
            if (is_leaf(cur)) {
                result = head_term(pool, cur);
            }
            else if (pap1_kind(cur->entry)) {
                back_stack_push(&bs, (BackItem){BACK_P1_DONE, cur, NULL});
                back_stack_push(&bs, (BackItem){BACK_VISIT, cur->payload.s1.x, NULL});
            }
            else if (pap2_kind(cur->entry)) {
                back_stack_push(&bs, (BackItem){BACK_P2_BUILD, cur, NULL});
                back_stack_push(&bs, (BackItem){BACK_P2_X_DONE, cur, NULL});
                back_stack_push(&bs, (BackItem){BACK_VISIT, cur->payload.s2.x, NULL});
            }
            else if (cur->entry == entry_AP) {
                back_stack_push(&bs, (BackItem){BACK_AP_BUILD, cur, NULL});
                back_stack_push(&bs, (BackItem){BACK_AP_LEFT_DONE, cur, NULL});
                back_stack_push(&bs, (BackItem){BACK_VISIT, cur->payload.ap.f, NULL});
            }
            else {
                fprintf(stderr, "STG: cannot read back a closure of this kind\n");
                abort();
            }
            break;
        }
        
        case BACK_P1_DONE: {
            SKITerm *x = result;
            result = ski_app(pool, head_term(pool, item.closure), x);
            break;
        }
        
        case BACK_P2_X_DONE: {
            /* x done, save and do y */
            STACK_TOP(&bs.s, BackItem).left_result = result;
            back_stack_push(&bs, (BackItem){BACK_VISIT, item.closure->payload.s2.y, NULL});
            break;
        }
        
        case BACK_P2_BUILD: {
            SKITerm *x = item.left_result;
            SKITerm *y = result;
            result = ski_app(pool, ski_app(pool, head_term(pool, item.closure), x), y);
            break;
        }
        
        case BACK_AP_LEFT_DONE: {
            /* f done, save and do arg */
            STACK_TOP(&bs.s, BackItem).left_result = result;
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
    
    /* The singletons at the start of every space are rebuilt at the start of the to-space: a pointer to one, in
     * either space, becomes the same singleton there (so the old spaces can go when the heap grows) */
    for (int sp_i = 0; sp_i < 2; sp_i++) {
        char *base = (char*)stg->space[sp_i];
        if ((char*)from >= base && (char*)from < base + SINGLETON_WORDS * WORD)
            return (Closure*)((char*)stg->gc_to + ((char*)from - base));
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
    EntryCode e = c->entry;
    if (pap1_kind(e) || e == entry_IND) {
        c->payload.s1.x = gc_copy(stg, c->payload.s1.x, to_hp);        /* one pointer at word 1 (PRIM1's op is a datum) */
    } else if (pap2_kind(e) || e == entry_AP) {
        c->payload.s2.x = gc_copy(stg, c->payload.s2.x, to_hp);
        c->payload.s2.y = gc_copy(stg, c->payload.s2.y, to_hp);
    }
    /* leaves, words and primitives have no pointers to scavenge */
}

/*
 * Cheney's algorithm - the main GC loop
 */
/* copy the live data out of the active space into to_base (a space of at least the live size); the caller makes
   to_base the active space */
static void stg_collect(STG *stg, Closure *to_base) {
    stg->gc_count++;
    stg->bytes_copied = 0;
    
    stg->gc_to = to_base;
    Closure *to_hp = to_base;  /* allocation pointer in to-space */
    Closure *scan = to_base;    /* scan pointer for scavenging */
    
    /* First, the singletons at the start of the new space (every space keeps them) */
    singletons_build(stg, to_base);
    to_hp = (Closure*)((char*)to_base + SINGLETON_WORDS * WORD);
    scan = to_hp;  /* don't scavenge the singletons */
    
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
        for (size_t i = 0; i < stg->ws_root->s.n; i++) {
            WorkItem *w = &STACK_AT(&stg->ws_root->s, WorkItem, i);
            w->closure = gc_copy(stg, w->closure, &to_hp);
            w->saved_x = gc_copy(stg, w->saved_x, &to_hp);
        }
    }
    
    /* Copy roots: pending term_to_stg conversion items */
    if (stg->cs_root) {
        for (size_t i = 0; i < stg->cs_root->s.n; i++) {
            ConvItem *ci = &STACK_AT(&stg->cs_root->s, ConvItem, i);
            ci->left_result = gc_copy(stg, ci->left_result, &to_hp);
        }
    }
    
    /* Cheney loop: scan copied closures and copy their children */
    while (scan < to_hp) {
        gc_scavenge(stg, scan, &to_hp);
        int size = closure_size(scan);
        scan = (Closure*)((char*)scan + size * WORD);
    }
    
    stg->hp = to_hp;
    
#if 0
    size_t used = (char*)to_hp - (char*)to_base;
    fprintf(stderr, "GC #%llu: copied %llu bytes, %zu bytes used\n", 
            stg->gc_count, stg->bytes_copied, used);
#endif
}
static void stg_gc(STG *stg) {
    int to_space = 1 - stg->active_space;
    stg_collect(stg, stg->space[to_space]);
    stg->active_space = to_space;
    stg->heap_end = (Closure*)((char*)stg->space[to_space] + stg->heap_size);
}

/* After a collection the live data and the pending request must fit in half a space - or the next collection comes
 * at once, and the one after. Otherwise both spaces double until they do, and the live data moves into the new pair.
 * The only limit is the memory layer's. */
static void stg_make_room(STG *stg, size_t need_bytes) {
    size_t live = (size_t)((char*)stg->hp - (char*)stg->space[stg->active_space]);
    if ((live + need_bytes) * 2 <= stg->heap_size) return;
    size_t size = stg->heap_size;
    while ((live + need_bytes) * 2 > size) {
        if (size > SIZE_MAX / 4) resource_die("STG: a heap of %zu live bytes", live + need_bytes);
        size *= 2;
    }
    Closure *a = rmalloc(size), *b = rmalloc(size);
    stg_collect(stg, a);
    free(stg->space[0]); free(stg->space[1]);
    stg->space[0] = a; stg->space[1] = b; stg->active_space = 0;
    stg->heap_size = size;
    stg->heap_end = (Closure*)((char*)a + size);
}

/*
 * Initialize STG machine with two semi-spaces
 */
static void stg_init(void) {
    if (g_stg) return;
    
    g_stg = rmalloc(sizeof(STG));
    memset(g_stg, 0, sizeof(STG));
    
    g_stg->heap_size = HEAP_SIZE;
    g_stg->space[0] = rmalloc(HEAP_SIZE);
    g_stg->space[1] = rmalloc(HEAP_SIZE);
    g_stg->active_space = 0;
    g_stg->hp = g_stg->space[0];
    g_stg->heap_end = (Closure*)((char*)g_stg->space[0] + HEAP_SIZE);
    
    g_stg->stack = rmalloc(STACK_SIZE);
    g_stg->stack_base = (Closure**)((char*)g_stg->stack + STACK_SIZE);
    g_stg->sp = g_stg->stack_base;
    
    g_stg->update_size = 1024;
    g_stg->update_stack = rmalloc(g_stg->update_size * sizeof(g_stg->update_stack[0]));
    g_stg->update_sp = 0;
    
    /* Pre-build the singletons */
    singletons_build(g_stg, g_stg->space[0]);
    g_stg->hp = (Closure*)((char*)g_stg->space[0] + SINGLETON_WORDS * WORD);
    
    g_stg->gc_count = 0;
}

/*
 * Reset STG machine for new evaluation
 */
static void stg_reset(void) {
    /* Reset to space 0, preserving primitives at start */
    g_stg->active_space = 0;
    g_stg->hp = (Closure*)((char*)g_stg->space[0] + SINGLETON_WORDS * WORD);
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
    
    /* Re-establish the singletons at the start of space 0 */
    singletons_build(g_stg, g_stg->space[0]);
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
    stg->extra_roots[0] = P;
    stg_reserve(stg, words);   /* the heap grows to hold it */
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

/* ========================================================================
 * The monadic driver (eezo -m; see io.h and the stdlib's io.eezo)
 * ======================================================================== */

/* a Church numeral n = succ^n (K I); the caller reserved MO_NUMERAL_WORDS(n) */
#define MO_NUMERAL_WORDS(n) (2 + 12 + 3 * (n))
static Closure *mo_ki(STG *stg) {
    Closure *ki = stg_alloc(stg, 2);
    ki->entry = entry_K1;
    ki->payload.k1.x = stg->prim_I;
    return ki;
}
static Closure *mo_succ(STG *stg) {   /* S (S (K S) K): 12 words */
    return io_ap(stg, stg->prim_S, io_ap(stg, io_ap(stg, stg->prim_S, io_ap(stg, stg->prim_K, stg->prim_S)), stg->prim_K));
}
static Closure *mo_numeral(STG *stg, long n) {
    Closure *c = mo_ki(stg);
    if (n == 0) return c;
    Closure *succ = mo_succ(stg);
    for (long k = 0; k < n; k++) c = io_ap(stg, succ, c);
    return c;
}
/* the value of the Church numeral h (h K S = K^n S), or -1 when it is not one; uses extra_roots[3] */
static long mo_value(STG *stg, Closure *h) {
    stg->extra_roots[3] = h;
    stg_reserve(stg, 6);
    h = stg->extra_roots[3];
    stg->extra_roots[3] = NULL;
    Closure *t = stg_enter(stg, io_ap(stg, io_ap(stg, h, stg->prim_K), stg->prim_S));
    long n = 0;
    while (t->entry == entry_K1) {
        n++;
        t = stg_enter(stg, t->payload.k1.x);
    }
    return t->entry == entry_S ? n : -1;
}

int stg_run_monad(SKIPool *pool, SKITerm *prog) {
    (void)pool;
    stg_init();
    stg_reset();
    STG *stg = g_stg;
    if (setjmp(stg->exit_jmp)) {
        io_flush();
        return 1;
    }
    Closure *t = term_to_stg(stg, prog);
    for (;;) {
        Closure *v = stg_enter(stg, t);                          /* the step e -> a -> e | e -> a -> a g k x, in WHNF */
        /* the tag: v 0 (K (K (K 1))); built beside v: 0 (2), 1 (2 + 12 + 3), the selector (9), the applications (6) */
        stg->extra_roots[0] = v;
        stg_reserve(stg, 34);
        v = stg->extra_roots[0];
        Closure *n0 = mo_ki(stg);
        Closure *n1 = io_ap(stg, mo_succ(stg), mo_ki(stg));
        Closure *sel0 = io_ap(stg, stg->prim_K, io_ap(stg, stg->prim_K, io_ap(stg, stg->prim_K, n1)));
        long tag = mo_value(stg, io_ap(stg, io_ap(stg, v, n0), sel0));
        if (tag == 0) break;                                     /* done: the result is not observed */
        if (tag != 1) { io_flush(); fprintf(stderr, "io: the program is not a step of the monad's protocol\n"); return 1; }
        /* the fields: v 0 (\g k x -> g), v 0 (\g k x -> k), v 0 (\g k x -> x): 2 + 9 + 3 + 5 + 3 * 6 = 37 words */
        v = stg->extra_roots[0];
        stg_reserve(stg, 37);
        v = stg->extra_roots[0];
        stg->extra_roots[0] = NULL;
        n0 = mo_ki(stg);
        Closure *kk = io_ap(stg, stg->prim_K, stg->prim_K);
        Closure *sel1 = io_ap(stg, io_ap(stg, stg->prim_S, kk), stg->prim_K);   /* S (K K) K */
        Closure *sel2 = kk;                                                     /* K K */
        Closure *sel3 = io_ap(stg, stg->prim_K, mo_ki(stg));                    /* K (K I) */
        Closure *g = io_ap(stg, io_ap(stg, v, n0), sel1);
        Closure *k = io_ap(stg, io_ap(stg, v, n0), sel2);
        Closure *x = io_ap(stg, io_ap(stg, v, n0), sel3);
        stg->extra_roots[0] = k; stg->extra_roots[1] = x; stg->extra_roots[2] = g;
        stg_reserve(stg, 2 + 12 + 6 + 9);
        k = stg->extra_roots[0]; x = stg->extra_roots[1]; g = stg->extra_roots[2];
        stg->extra_roots[2] = NULL;
        n0 = mo_ki(stg);
        Closure *succ = mo_succ(stg);
        n1 = io_ap(stg, succ, n0);
        Closure *n2 = io_ap(stg, succ, n1);
        long code = mo_value(stg, io_ap(stg, io_ap(stg, io_ap(stg, g, n0), n1), n2));   /* which handler the action selects */
        k = stg->extra_roots[0]; x = stg->extra_roots[1];
        if (code == 0) {                                         /* putc */
            long b = mo_value(stg, x);
            if (b < 0 || b > 255) { io_flush(); fprintf(stderr, "io: putc of a value that is not a byte\n"); return 1; }
            io_put_byte((int)b);
            stg_reserve(stg, 2 + 3);
            k = stg->extra_roots[0];
            stg->extra_roots[0] = stg->extra_roots[1] = NULL;
            t = io_ap(stg, k, mo_ki(stg));
        } else if (code == 1) {                                  /* getc */
            io_flush();
            int c = getchar();
            long b = c == EOF ? 256 : c;
            stg_reserve(stg, MO_NUMERAL_WORDS(b) + 3);
            k = stg->extra_roots[0];
            stg->extra_roots[0] = stg->extra_roots[1] = NULL;
            t = io_ap(stg, k, mo_numeral(stg, b));
        } else if (code == 2) {                                  /* exit */
            long n = mo_value(stg, x);
            io_flush();
            return n < 0 ? 1 : (int)n;
        } else {
            io_flush(); fprintf(stderr, "io: the action is not one the driver has (%ld)\n", code); return 1;
        }
    }
    io_flush();
    return 0;
}
