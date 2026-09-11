/*
 * stg.h - STG Machine for SKI Combinators
 *
 * Spineless Tagless G-machine implementation for SKI reduction.
 */
#ifndef EEZO_STG_H
#define EEZO_STG_H

#include <libeezo/term.h>

/* Reduce using STG machine (C interpreter with Cheney GC).
 * whnf = 0: full normal form; whnf = 1: weak head normal form only. */
SKITerm *stg_reduce(SKIPool *pool, SKITerm *term, i64 *steps, int whnf);

#endif /* EEZO_STG_H */
