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
#include "stg.h"

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
    fprintf(stderr, "  -f FORMAT     Input format: bcl (default), jot, jomplement\n");
    fprintf(stderr, "  -o FORMAT     Output format: bcl (default), jot, jomplement, ski\n");
    fprintf(stderr, "  -s            Use simple interpreter (default: STG machine)\n");
    fprintf(stderr, "  -v            Verbose output\n");
    fprintf(stderr, "  -h            Show this help\n");
    fprintf(stderr, "\nInput is ASCII '0'/'1' bits read from stdin.\n");
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
    Format in_fmt = FMT_BCL;
    Format out_fmt = FMT_BCL;
    int use_simple = 0;
    int verbose = 0;
    int out_ski = 0;
    
    /* Parse arguments */
    for (int i = 1; i < argc; i++) {
        if (strcmp(argv[i], "-h") == 0 || strcmp(argv[i], "--help") == 0) {
            usage(argv[0]);
            return 0;
        } else if (strcmp(argv[i], "-v") == 0) {
            verbose = 1;
        } else if (strcmp(argv[i], "-s") == 0) {
            use_simple = 1;
        } else if (strcmp(argv[i], "-f") == 0) {
            if (++i >= argc) {
                fprintf(stderr, "Missing argument for -f\n");
                return 1;
            }
            if (strcmp(argv[i], "bcl") == 0) {
                in_fmt = FMT_BCL;
            } else if (strcmp(argv[i], "jot") == 0) {
                in_fmt = FMT_JOT;
            } else if (strcmp(argv[i], "jomplement") == 0) {
                in_fmt = FMT_JOMPLEMENT;
            } else {
                fprintf(stderr, "Unknown format: %s\n", argv[i]);
                return 1;
            }
        } else if (strcmp(argv[i], "-o") == 0) {
            if (++i >= argc) {
                fprintf(stderr, "Missing argument for -o\n");
                return 1;
            }
            if (strcmp(argv[i], "bcl") == 0) {
                out_fmt = FMT_BCL;
            } else if (strcmp(argv[i], "jot") == 0) {
                out_fmt = FMT_JOT;
            } else if (strcmp(argv[i], "jomplement") == 0) {
                out_fmt = FMT_JOMPLEMENT;
            } else if (strcmp(argv[i], "ski") == 0) {
                out_ski = 1;
            } else {
                fprintf(stderr, "Unknown format: %s\n", argv[i]);
                return 1;
            }
        } else {
            fprintf(stderr, "Unknown option: %s\n", argv[i]);
            usage(argv[0]);
            return 1;
        }
    }
    
    /* Read input */
    u64 nbits;
    u8 *bits = read_bits(stdin, &nbits);
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
    switch (in_fmt) {
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
    
    /* Evaluate */
    i64 steps;
    SKITerm *result;
    
    if (use_simple) {
        if (verbose) fprintf(stderr, "Using simple interpreter...\n");
        steps = ski_reduce(&pool, &term, 0);
        result = term;
    } else {
        if (verbose) fprintf(stderr, "Using STG machine...\n");
        result = stg_reduce(&pool, term, &steps);
        ski_unref(&pool, term);
    }
    
    if (verbose) {
        fprintf(stderr, "Reduced (%lld steps)\n", (long long)steps);
        fprintf(stderr, "Result: ");
        ski_fprint(stderr, result);
        fprintf(stderr, "\n");
    }
    
    /* Output result */
    if (out_ski) {
        ski_fprint(stdout, result);
        printf("\n");
    } else {
        output_result(result, out_fmt);
    }
    
    ski_unref(&pool, result);
    pool_free(&pool);
    return 0;
}
