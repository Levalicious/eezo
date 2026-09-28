/*
 * stg.h - STG Machine for SKI Combinators
 *
 * Spineless Tagless G-machine implementation for SKI reduction.
 */
#ifndef EEZO_STG_H
#define EEZO_STG_H

#include <stddef.h>
#include <libeezo/term.h>

/* Reduce using STG machine (C interpreter with Cheney GC).
 * whnf = 0: full normal form; whnf = 1: weak head normal form only. */
SKITerm *stg_reduce(SKIPool *pool, SKITerm *term, i64 *steps, int whnf);

/* Run prog as a Lazy-K stream transformer (see io.h): the input bytes
 * become the input stream, output bytes go to stdout as they are
 * produced. Returns the process exit status. */
int stg_run_io(SKIPool *pool, SKITerm *prog, const u8 *data, size_t len);
int stg_run_monad(SKIPool *pool, SKITerm *prog);   /* the monadic driver (eezo -m; io.h) */

#endif /* EEZO_STG_H */
