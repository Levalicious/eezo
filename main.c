/*
 * main.c - Eezo evaluator
 *
 * Evaluates pre-compiled BCL/Jot/Jomplement programs.
 * Like java vs javac - this is the runtime.
 */
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
    u8 *bits = malloc(cap);
    if (!bits) return NULL;
    
    u64 nbits = 0;
    int c;
    
    while ((c = fgetc(f)) != EOF) {
        if (c == '0' || c == '1') {
            if (nbits >= cap * 8) {
                cap *= 2;
                u8 *newbits = realloc(bits, cap);
                if (!newbits) {
                    free(bits);
                    return NULL;
                }
                bits = newbits;
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

/* Output result in specified format */
static void output_result(SKITerm *term, Format fmt) {
    if (fmt == FMT_BCL) {
        u64 size_bits = bcl_size(term);
        u32 buf_size = (size_bits + 7) / 8 + 8;
        u8 *buf = malloc(buf_size);
        if (!buf) {
            fprintf(stderr, "Out of memory\n");
            return;
        }
        memset(buf, 0, buf_size);
        
        BclBuffer bb;
        bcl_buffer_init(&bb, buf, buf_size * 8);
        if (bcl_emit(term, &bb)) {
            i32 bits = (i32)bcl_buffer_len(&bb);
            for (int b = 0; b < bits; b++) {
                int byte_idx = b / 8;
                int bit_idx = 7 - (b % 8);
                printf("%d", (buf[byte_idx] >> bit_idx) & 1);
            }
            printf("\n");
        } else {
            fprintf(stderr, "BCL emission failed\n");
        }
        free(buf);
    } else if (fmt == FMT_JOT) {
        u64 size_bits = jot_size(term);
        u32 buf_size = (size_bits + 7) / 8 + 8;
        u8 *buf = malloc(buf_size);
        if (!buf) {
            fprintf(stderr, "Out of memory\n");
            return;
        }
        memset(buf, 0, buf_size);
        
        i32 bits = jot_emit(term, buf, buf_size);
        if (bits > 0) {
            for (int b = 0; b < bits; b++) {
                int byte_idx = b / 8;
                int bit_idx = 7 - (b % 8);
                printf("%d", (buf[byte_idx] >> bit_idx) & 1);
            }
            printf("\n");
        } else {
            fprintf(stderr, "Jot emission failed\n");
        }
        free(buf);
    } else if (fmt == FMT_JOMPLEMENT) {
        u64 size_bits = jot_size(term);
        u32 buf_size = (size_bits + 7) / 8 + 8;
        u8 *buf = malloc(buf_size);
        if (!buf) {
            fprintf(stderr, "Out of memory\n");
            return;
        }
        memset(buf, 0, buf_size);
        
        i32 bits = jomplement_emit(term, buf, buf_size);
        if (bits > 0) {
            for (int b = 0; b < bits; b++) {
                int byte_idx = b / 8;
                int bit_idx = 7 - (b % 8);
                printf("%d", (buf[byte_idx] >> bit_idx) & 1);
            }
            printf("\n");
        } else {
            fprintf(stderr, "Jomplement emission failed\n");
        }
        free(buf);
    }
}

int main(int argc, char **argv) {
    Format fmt = FMT_BCL;
    int use_simple = 0;
    int io_mode = 0;
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
    pool_init(&pool, 1000000);
    
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
    }
    
    free(bits);
    
    if (!term) {
        fprintf(stderr, "Parse failed\n");
        pool_free(&pool);
        return 1;
    }
    
    if (verbose) {
        fprintf(stderr, "Input: ");
        ski_fprint(stderr, term);
        fprintf(stderr, "\n");
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
            u32 code_cap = 64 * 1024;
            u8 *code_buf = malloc(code_cap);
            NativeEmit e;
            native_emit_init(&e, code_buf, code_cap, OUTPUT_BCL);
            e.io_mode = 1;
            native_emit_runtime(&e);
            NativeJIT *jit = native_jit_prepare(&e, heap_size);
            if (!jit || native_jit_load_term(jit, term) != 0) {
                fprintf(stderr, "JIT preparation failed\n");
                rc = 1;
            } else {
                /* the child reads the data from stdin itself */
                rc = native_jit_run(jit);
            }
            native_jit_free(jit);
            free(code_buf);
        } else if (use_simple) {
            rc = io_run_simple(&pool, term, data, data_len);
        } else {
            rc = stg_run_io(&pool, term, data, data_len);
        }
        free(data);
        pool_free(&pool);
        return rc;
    }
    
    /* Evaluate */
    i64 steps = 0;  /* 0 = no step limit */
    SKITerm *result;
    
    if (use_native) {
        if (verbose) fprintf(stderr, "Using native JIT...\n");
        
        /* Allocate code buffer */
        u32 code_cap = 64 * 1024;
        u8 *code_buf = malloc(code_cap);
        if (!code_buf) {
            fprintf(stderr, "Out of memory\n");
            pool_free(&pool);
            return 1;
        }
        
        /* Initialize and emit runtime */
        NativeEmit e;
        OutputFormat native_fmt = OUTPUT_BCL;
        if (fmt == FMT_JOT) native_fmt = OUTPUT_JOT;
        else if (fmt == FMT_JOMPLEMENT) native_fmt = OUTPUT_JOMPLEMENT;
        native_emit_init(&e, code_buf, code_cap, native_fmt);
        e.nf_mode = whnf ? 0 : 1;
        native_emit_runtime(&e);
        
        /* Prepare JIT */
        NativeJIT *jit = native_jit_prepare(&e, heap_size);
        if (!jit) {
            fprintf(stderr, "JIT preparation failed\n");
            free(code_buf);
            pool_free(&pool);
            return 1;
        }
        
        /* Load term onto heap */
        if (native_jit_load_term(jit, term) != 0) {
            fprintf(stderr, "Term too large for heap\n");
            native_jit_free(jit);
            free(code_buf);
            pool_free(&pool);
            return 1;
        }
        
        /* Run - forks, child executes and exits */
        int exit_status = native_jit_run(jit);
        
        if (verbose) {
            fprintf(stderr, "Native JIT exited with status %d\n", exit_status);
        }
        
        native_jit_free(jit);
        free(code_buf);
        ski_unref(&pool, term);
        pool_free(&pool);
        
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
    pool_free(&pool);
    return 0;
}
