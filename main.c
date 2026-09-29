#include <libeezo/mem.h>
/*
 * main.c - Eezo evaluator
 *
 * Evaluates pre-compiled BCL/Jot/Jomplement programs.
 * Like java vs javac - this is the runtime.
 */
#include <signal.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdbool.h>
#include <libeezo/term.h>
#include <libeezo/bcl.h>
#include <libeezo/jomplement.h>
#include <libeezo/native.h>
#include "stg.h"
#include "io.h"

/* Input format */
typedef enum {
    FMT_BCL,
    FMT_JOT,
    FMT_JOMPLEMENT,
    FMT_XBCL,
} Format;

static void usage(const char *prog) {
    fprintf(stderr, "Usage: %s [options] < input\n", prog);
    fprintf(stderr, "\nEezo evaluator - executes pre-compiled SKI programs\n");
    fprintf(stderr, "\nOptions:\n");
    fprintf(stderr, "  -f FORMAT     Format: bcl (default), jot, jomplement\n");
    fprintf(stderr, "  -s            Use simple interpreter (default: STG machine)\n");
    fprintf(stderr, "  -n            Use native JIT (x86_64)\n");
    fprintf(stderr, "  -i            Stream I/O mode (Lazy-K): the program, given as a FILE argument,\n");
    fprintf(stderr, "                maps the byte stream on stdin to the byte stream on stdout\n");
    fprintf(stderr, "  -m            Monadic I/O mode: the program is run(m) of the stdlib's io.eezo, a value of\n");
    fprintf(stderr, "                the IO monad; the driver performs its actions (putc, getc, exit)\n");
    fprintf(stderr, "  -H BYTES      (with -n) initial semispace size, default 16MiB; grows on demand\n");
    fprintf(stderr, "  -N MODE       Normalization: nf (default, full normal form) or whnf\n");
    fprintf(stderr, "                (weak head normal form: head reduction only)\n");
    fprintf(stderr, "  -v            Verbose output\n");
    fprintf(stderr, "  -h            Show this help\n");
    fprintf(stderr, "\nThe program is ASCII '0'/'1' bits, read from FILE if given, else from stdin.\n");
}

/* Read ASCII bits from file into packed bytes */
static u8 *read_bits(FILE *f, u64 *out_nbits) {
    size_t cap = 8192;
    u8 *bits = rmalloc(cap);
    
    u64 nbits = 0;
    int c;
    
    while ((c = fgetc(f)) != EOF) {
        if (c == '0' || c == '1') {
            if (nbits >= cap * 8) {
                cap *= 2;
                bits = rrealloc(bits, cap);
            }
            u64 byte_idx = nbits / 8;
            int bit_idx = 7 - (nbits % 8);
            if (bit_idx == 7) bits[byte_idx] = 0;
            if (c == '1') bits[byte_idx] |= (1 << bit_idx);
            nbits++;
        }
        /* Ignore whitespace, newlines, etc. */
    }
    
    *out_nbits = nbits;
    return bits;
}

/* Output result in specified format: the bits, emitted into the growable buffer (bcl.h), as ASCII */
static void output_result(SKITerm *term, Format fmt) {
    BclBuffer bb;
    bcl_buffer_init(&bb);
    bool ok = fmt == FMT_XBCL ? xbcl_emit(term, &bb)
            : fmt == FMT_BCL ? bcl_emit(term, &bb)
            : fmt == FMT_JOT ? jot_emit(term, &bb)
            : jomplement_emit(term, &bb);
    if (ok) {
        const u8 *buf = bcl_buffer_data(&bb);
        for (u64 b = 0; b < bcl_buffer_len(&bb); b++) putchar('0' + ((buf[b / 8] >> (7 - b % 8)) & 1));
        printf("\n");
    } else {
        fprintf(stderr, "%s emission failed\n", fmt == FMT_XBCL || fmt == FMT_BCL ? "BCL" : fmt == FMT_JOT ? "Jot" : "Jomplement");
    }
    bcl_buffer_drop(&bb);
}

/* The term onto the JIT's heap. The native runtime's heaps are 32 bits wide (their sizes): a term needing more is
   past that width, reported as the resource limit it is */
static void native_jit_load_or_die(NativeJIT *jit, SKITerm *term) {
    if (native_jit_load_term(jit, term) != 0) resource_die("the term needs a heap past the native runtime's 4 GB width");
}

int main(int argc, char **argv) {
    /* The classic pipe behaviour whatever the parent left us: a program streaming to a reader that has gone away dies
       of SIGPIPE (exit 141). A CI runner's shell ignores SIGPIPE, and an inherited SIG_IGN turned the death into an
       endless loop of failed writes (the io suite's 'ones', 2026-09-28). */
    signal(SIGPIPE, SIG_DFL);
    mem_init("eezo", "EEZO_MAX_ALLOC");   /* the one memory layer (libeezo/mem.h): its failure path and budget */
    Format fmt = FMT_BCL;
    int use_simple = 0;
    int io_mode = 0;
    int monad_mode = 0;
    const char *prog_path = NULL;
    int use_native = 0;
    int verbose = 0;
    int whnf = 0;
    u32 heap_size = NATIVE_DEFAULT_HEAP_SIZE;
    
    /* Parse arguments */
    for (int i = 1; i < argc; i++) {
        if (strcmp(argv[i], "-h") == 0 || strcmp(argv[i], "--help") == 0) {
            usage(argv[0]);
            return 0;
        } else if (strcmp(argv[i], "-v") == 0) {
            verbose = 1;
        } else if (strcmp(argv[i], "-s") == 0) {
            use_simple = 1;
        } else if (strcmp(argv[i], "-i") == 0) {
            io_mode = 1;
        } else if (strcmp(argv[i], "-m") == 0) {
            monad_mode = 1;
        } else if (strcmp(argv[i], "-n") == 0) {
            use_native = 1;
        } else if (strcmp(argv[i], "-H") == 0) {
            if (++i >= argc) {
                fprintf(stderr, "Missing argument for -H\n");
                return 1;
            }
            heap_size = (u32)strtoul(argv[i], NULL, 0);
            if (heap_size < 4096) {
                fprintf(stderr, "Heap size too small: %s\n", argv[i]);
                return 1;
            }
        } else if (strcmp(argv[i], "-N") == 0) {
            if (++i >= argc) {
                fprintf(stderr, "Missing argument for -N\n");
                return 1;
            }
            if (strcmp(argv[i], "nf") == 0) {
                whnf = 0;
            } else if (strcmp(argv[i], "whnf") == 0) {
                whnf = 1;
            } else {
                fprintf(stderr, "Unknown normalization mode: %s (nf|whnf)\n", argv[i]);
                return 1;
            }
        } else if (strcmp(argv[i], "-f") == 0) {
            if (++i >= argc) {
                fprintf(stderr, "Missing argument for -f\n");
                return 1;
            }
            if (strcmp(argv[i], "bcl") == 0) {
                fmt = FMT_BCL;
            } else if (strcmp(argv[i], "jot") == 0) {
                fmt = FMT_JOT;
            } else if (strcmp(argv[i], "jomplement") == 0) {
                fmt = FMT_JOMPLEMENT;
            } else if (strcmp(argv[i], "xbcl") == 0) {
                fmt = FMT_XBCL;
            } else {
                fprintf(stderr, "Unknown format: %s\n", argv[i]);
                return 1;
            }
        } else if (argv[i][0] != '-' && !prog_path) {
            prog_path = argv[i];
        } else {
            fprintf(stderr, "Unknown option: %s\n", argv[i]);
            usage(argv[0]);
            return 1;
        }
    }
    
    /* Read input */
    u64 nbits;
    FILE *prog_in = stdin;
    if (prog_path) {
        prog_in = fopen(prog_path, "r");
        if (!prog_in) {
            perror(prog_path);
            return 1;
        }
    } else if (io_mode) {
        fprintf(stderr, "-i reads the program's input from stdin: give the program as a file argument\n");
        return 1;
    }
    u8 *bits = read_bits(prog_in, &nbits);
    if (prog_in != stdin) fclose(prog_in);
    if (!bits || nbits == 0) {
        fprintf(stderr, "No input\n");
        free(bits);
        return 1;
    }
    
    if (verbose) {
        fprintf(stderr, "Read %llu bits\n", (unsigned long long)nbits);
    }
    
    /* Initialize term pool */
    SKIPool pool;
    ski_pool_init(&pool);
    
    /* Parse input */
    BclStream s;
    bcl_stream_init(&s, bits, nbits);
    
    SKITerm *term = NULL;
    switch (fmt) {
    case FMT_BCL:
        term = bcl_parse(&pool, &s);
        if (verbose) fprintf(stderr, "Parsed BCL\n");
        break;
    case FMT_JOT:
        term = jot_parse(&pool, &s);
        if (verbose) fprintf(stderr, "Parsed Jot\n");
        break;
    case FMT_JOMPLEMENT:
        term = jomplement_parse(&pool, &s);
        if (verbose) fprintf(stderr, "Parsed Jomplement\n");
        break;
    case FMT_XBCL:
        term = xbcl_parse(&pool, &s);
        if (verbose) fprintf(stderr, "Parsed XBCL\n");
        break;
    }
    
    free(bits);
    
    if (!term) {
        fprintf(stderr, "Parse failed\n");
        ski_pool_drop(&pool);
        return 1;
    }
    
    if (verbose) {
        fprintf(stderr, "Input: ");
        ski_fprint(stderr, term);
        fprintf(stderr, "\n");
    }

    /* Monadic I/O mode: the program is run(m), a value of the IO monad; the driver performs its actions (io.h) */
    if (monad_mode) {
        int rc;
        if (use_native) {
            NativeEmit e;
            native_emit_init(&e, OUTPUT_BCL);
            e.io_mode = 2;
            native_emit_runtime(&e);
            NativeJIT *jit = native_jit_prepare(&e, heap_size);
            native_jit_load_or_die(jit, term);
            rc = native_jit_run(jit);            /* the child performs the actions itself */
            native_jit_free(jit);
            native_emit_drop(&e);
        }
        else if (use_simple) rc = io_run_monad_simple(&pool, term);
        else rc = stg_run_monad(&pool, term);
        ski_pool_drop(&pool);
        return rc;
    }

    /* Stream I/O mode: the program is a function from the input stream to
     * the output stream; the driver forces it one WHNF at a time (io.h). */
    if (io_mode) {
        size_t data_len = 0;
        u8 *data = NULL;
        int rc;
        /* the native child reads stdin itself; the C drivers take it here */
        if (!use_native) data = io_read_all_stdin(&data_len);
        if (use_native) {
            NativeEmit e;
            native_emit_init(&e, OUTPUT_BCL);
            e.io_mode = 1;
            native_emit_runtime(&e);
            NativeJIT *jit = native_jit_prepare(&e, heap_size);
            native_jit_load_or_die(jit, term);
            rc = native_jit_run(jit);   /* the child reads the data from stdin itself */
            native_jit_free(jit);
            native_emit_drop(&e);
        } else if (use_simple) {
            rc = io_run_simple(&pool, term, data, data_len);
        } else {
            rc = stg_run_io(&pool, term, data, data_len);
        }
        free(data);
        ski_pool_drop(&pool);
        return rc;
    }
    
    /* Evaluate */
    i64 steps = 0;  /* 0 = no step limit */
    SKITerm *result;
    
    if (use_native) {
        if (verbose) fprintf(stderr, "Using native JIT...\n");
        
        /* Initialize and emit runtime */
        NativeEmit e;
        OutputFormat native_fmt = OUTPUT_BCL;
        if (fmt == FMT_JOT) native_fmt = OUTPUT_JOT;
        else if (fmt == FMT_JOMPLEMENT) native_fmt = OUTPUT_JOMPLEMENT;
        else if (fmt == FMT_XBCL) native_fmt = OUTPUT_XBCL;
        native_emit_init(&e, native_fmt);
        e.nf_mode = whnf ? 0 : 1;
        native_emit_runtime(&e);
        
        /* Prepare JIT, load term onto heap */
        NativeJIT *jit = native_jit_prepare(&e, heap_size);
        native_jit_load_or_die(jit, term);
        
        /* Run - forks, child executes and exits */
        int exit_status = native_jit_run(jit);
        
        if (verbose) {
            fprintf(stderr, "Native JIT exited with status %d\n", exit_status);
        }
        
        native_jit_free(jit);
        native_emit_drop(&e);
        ski_unref(&pool, term);
        ski_pool_drop(&pool);
        
        /* Native JIT handles its own output, we just return the exit status */
        return exit_status;
        
    } else if (use_simple) {
        if (verbose) fprintf(stderr, "Using simple interpreter...\n");
        steps = ski_reduce_mode(&pool, &term, 0, whnf != 0);
        result = term;
    } else {
        if (verbose) fprintf(stderr, "Using STG machine...\n");
        result = stg_reduce(&pool, term, &steps, whnf);
        ski_unref(&pool, term);
    }
    
    if (verbose) {
        fprintf(stderr, "Reduced (%lld steps)\n", (long long)steps);
        fprintf(stderr, "Result: ");
        ski_fprint(stderr, result);
        fprintf(stderr, "\n");
    }
    
    /* Output result */
    output_result(result, fmt);
    
    ski_unref(&pool, result);
    ski_pool_drop(&pool);
    return 0;
}
