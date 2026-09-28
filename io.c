#include <libeezo/res.h>
/*
 * io.c - Lazy-K / WHNF stream I/O: stdin reading, the input stream as a
 * term, and the driver for the simple interpreter. See io.h.
 */
#include "io.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

u8 *io_read_all_stdin(size_t *len) {
    size_t cap = 65536, n = 0;
    u8 *buf = rmalloc(cap);
    if (!buf) resource_die("io: out of memory");
    for (;;) {
        if (n == cap) {
            cap *= 2;
            buf = rrealloc(buf, cap);
            if (!buf) resource_die("io: out of memory");
        }
        ssize_t r = read(0, buf + n, cap - n);
        if (r < 0) { perror("io: read"); exit(1); }
        if (r == 0) break;
        n += (size_t)r;
    }
    *len = n;
    return buf;
}

void io_put_byte(int b) {
    putchar(b);
}

void io_flush(void) {
    fflush(stdout);
}

static SKITerm *app(SKIPool *p, SKITerm *l, SKITerm *r) {
    SKITerm *t = ski_app(p, l, r);
    if (!t) { fprintf(stderr, "io: term pool exhausted\n"); exit(1); }
    return t;
}

/* cons x y = S (S I (K x)) (K y)  - the pair  f -> f x y.
 * Takes ownership of one reference to x and to y. */
static SKITerm *cons(SKIPool *p, SKITerm *x, SKITerm *y) {
    SKITerm *six = app(p, app(p, ski_s(p), ski_i(p)), app(p, ski_k(p), x));
    return app(p, app(p, ski_s(p), six), app(p, ski_k(p), y));
}

SKITerm *io_input_term(SKIPool *p, const u8 *data, size_t len) {
    /* Church numerals 0..256 as one shared chain:
     *   num[0] = K I,  num[k] = succ num[k-1],  succ = S (S (K S) K) */
    SKITerm *succ = app(p, ski_s(p), app(p, app(p, ski_s(p), app(p, ski_k(p), ski_s(p))), ski_k(p)));
    SKITerm *num[257];
    num[0] = app(p, ski_k(p), ski_i(p));
    for (int k = 1; k <= 256; k++)
        num[k] = app(p, ski_ref(succ), ski_ref(num[k - 1]));
    ski_unref(p, succ);
    
    /* EOF: an infinite stream of 256 - a cycle. The back edge holds a
     * reference, so the cell lives until the pool is freed. */
    SKITerm *eof = cons(p, ski_ref(num[256]), NULL);
    eof->app.right->app.right = ski_ref(eof);
    
    /* The data, back to front, ending in the EOF stream */
    SKITerm *s = eof;
    for (size_t i = len; i > 0; i--)
        s = cons(p, ski_ref(num[data[i - 1]]), s);
    
    for (int k = 0; k <= 256; k++) ski_unref(p, num[k]);
    return s;
}

/* Reduce *t to weak head normal form in place */
static SKITerm *whnf(SKIPool *p, SKITerm *t) {
    if (ski_reduce_mode(p, &t, 0, true) < 0) {
        io_flush();
        fprintf(stderr, "io: reduction failed (term pool exhausted?)\n");
        exit(1);
    }
    return t;
}

int io_run_simple(SKIPool *p, SKITerm *prog, const u8 *data, size_t len) {
    SKITerm *o = app(p, prog, io_input_term(p, data, len));
    for (;;) {
        o = whnf(p, o);                                                   /* the output cell */
        SKITerm *h = whnf(p, app(p, ski_ref(o), ski_k(p)));                /* head = o K */
        SKITerm *t = whnf(p, app(p, app(p, h, ski_k(p)), ski_s(p)));       /* h K S */
        long n = 0;
        while (t->tag == TERM_APP && t->app.left->tag == TERM_K) {         /* K1[u]: one more */
            n++;
            SKITerm *u = ski_ref(t->app.right);
            ski_unref(p, t);
            t = whnf(p, u);
        }
        if (t->tag != TERM_S) {
            io_flush();
            fprintf(stderr, "io: output element is not a numeral\n");
            return 1;
        }
        ski_unref(p, t);
        if (n >= 256) {
            io_flush();
            return (int)(n - 256);
        }
        io_put_byte((int)n);
        SKITerm *next = app(p, ski_ref(o), app(p, ski_k(p), ski_i(p)));    /* tail = o (K I) */
        ski_unref(p, o);
        o = next;
    }
}

/* ------------------------------------------------------------------------
 * The monadic driver (io.h; stdlib io.eezo)
 * ------------------------------------------------------------------------ */

/* the value of the Church numeral t (t K S = K^n S), or -1; takes ownership of t */
static long numeral(SKIPool *p, SKITerm *t) {
    t = whnf(p, app(p, app(p, t, ski_k(p)), ski_s(p)));
    long n = 0;
    while (t->tag == TERM_APP && t->app.left->tag == TERM_K) {
        n++;
        SKITerm *u = ski_ref(t->app.right);
        ski_unref(p, t);
        t = whnf(p, u);
    }
    int ok = t->tag == TERM_S;
    ski_unref(p, t);
    return ok ? n : -1;
}

int io_run_monad_simple(SKIPool *p, SKITerm *prog) {
    /* the numerals 0..256 (one shared chain); the step's readers: a step is e -> a -> e (done) or
       e -> a -> a g k x (act), so step 0 (\g k x -> 1) is the tag and step 0 (\g k x -> g) .. the fields */
    SKITerm *succ = app(p, ski_s(p), app(p, app(p, ski_s(p), app(p, ski_k(p), ski_s(p))), ski_k(p)));
    SKITerm *num[257];
    num[0] = app(p, ski_k(p), ski_i(p));
    for (int k = 1; k <= 256; k++) num[k] = app(p, ski_ref(succ), ski_ref(num[k - 1]));
    ski_unref(p, succ);
    SKITerm *kk = app(p, ski_k(p), ski_k(p));                                                      /* K K */
    SKITerm *sel0 = app(p, ski_k(p), app(p, ski_k(p), app(p, ski_k(p), ski_ref(num[1]))));       /* K (K (K 1)): the tag */
    SKITerm *sel1 = app(p, app(p, ski_s(p), ski_ref(kk)), ski_k(p));                              /* S (K K) K = \g k x -> g */
    SKITerm *sel2 = kk;                                                                           /* K K = \g k x -> k */
    SKITerm *sel3 = app(p, ski_k(p), app(p, ski_k(p), ski_i(p)));                                 /* K (K I) = \g k x -> x */
    SKITerm *t = prog;
    int rc = 0;
    for (;;) {
        t = whnf(p, t);
        long tag = numeral(p, app(p, app(p, ski_ref(t), ski_ref(num[0])), ski_ref(sel0)));
        if (tag == 0) { ski_unref(p, t); break; }                                                 /* done: the result is not observed */
        if (tag != 1) { io_flush(); fprintf(stderr, "io: the program is not a step of the monad's protocol\n"); rc = 1; ski_unref(p, t); break; }
        SKITerm *g = app(p, app(p, ski_ref(t), ski_ref(num[0])), ski_ref(sel1));
        SKITerm *k = app(p, app(p, ski_ref(t), ski_ref(num[0])), ski_ref(sel2));
        SKITerm *x = app(p, app(p, ski_ref(t), ski_ref(num[0])), ski_ref(sel3));
        ski_unref(p, t);
        long code = numeral(p, app(p, app(p, app(p, g, ski_ref(num[0])), ski_ref(num[1])), ski_ref(num[2])));
        if (code == 0) {                                                                           /* putc */
            long b = numeral(p, x);
            if (b < 0 || b > 255) { io_flush(); fprintf(stderr, "io: putc of a value that is not a byte\n"); rc = 1; ski_unref(p, k); break; }
            io_put_byte((int)b);
            t = app(p, k, ski_ref(num[0]));
        } else if (code == 1) {                                                                    /* getc */
            ski_unref(p, x);
            io_flush();
            int c = getchar();
            t = app(p, k, ski_ref(num[c == EOF ? 256 : c]));
        } else if (code == 2) {                                                                    /* exit */
            long n = numeral(p, x);
            ski_unref(p, k);
            rc = n < 0 ? 1 : (int)n;
            break;
        } else {
            io_flush(); fprintf(stderr, "io: the action is not one the driver has (%ld)\n", code); rc = 1;
            ski_unref(p, k); ski_unref(p, x); break;
        }
    }
    io_flush();
    for (int k = 0; k <= 256; k++) ski_unref(p, num[k]);
    ski_unref(p, sel0); ski_unref(p, sel1); ski_unref(p, sel2); ski_unref(p, sel3);
    return rc;
}
