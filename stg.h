/*
 * stg.h - STG Machine for SKI Combinators
 *
 * Spineless Tagless G-machine implementation for SKI reduction.
 */
#ifndef EEZO_STG_H
#define EEZO_STG_H

#include <libeezo/term.h>

/* Reduce using STG machine (C interpreter with Cheney GC) */
SKITerm *stg_reduce(SKIPool *pool, SKITerm *term, i64 *steps);

#endif /* EEZO_STG_H */
