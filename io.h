/*
 * io.h - The Lazy-K / WHNF stream I/O model
 *
 * A program is a function from the input stream to the output stream.
 * Streams are pairs  f -> f x rest  (SK: S (S I (K x)) (K rest)) whose
 * elements are Church numerals; the input ends in an infinite stream of
 * 256, and an output element n >= 256 ends the program with exit status
 * n - 256. The driver never normalises anything beyond weak head normal
 * form: it forces the output cell, applies it to K for the head, reads
 * the numeral by applying it to the inert markers K and S and unfolding
 * the resulting K1 spine one WHNF at a time, then applies the cell to
 * K I for the tail. No host primitives are involved at any point.
 */
#ifndef EEZO_IO_H
#define EEZO_IO_H

#include <libeezo/types.h>
#include <libeezo/term.h>

/* Read all of fd 0. Returns a malloc'd buffer (NULL when *len == 0). */
u8 *io_read_all_stdin(size_t *len);

/* Buffered stdout bytes */
void io_put_byte(int b);
void io_flush(void);

/* The input stream as a (cyclic, numeral-sharing) SKITerm. */
SKITerm *io_input_term(SKIPool *p, const u8 *data, size_t len);

/* Run prog as a stream transformer on the simple interpreter.
 * Returns the process exit status. */
int io_run_simple(SKIPool *p, SKITerm *prog, const u8 *data, size_t len);

/* The monadic driver (eezo -m; stdlib io.eezo): the program is run(m), once in weak head normal form a Scott-encoded
   step e -> a -> e (done) or e -> a -> a g k x (an action g, a selector over putc, getc, exit, on the input x; the
   driver continues with k applied to the result). Reads stdin a byte at a time (256 at its end). */
int io_run_monad_simple(SKIPool *p, SKITerm *prog);

#endif
