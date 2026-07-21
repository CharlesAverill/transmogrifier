/* mealy.h -- interface to a Mealy machine compiled to Clight by Transmogrifier.
 *
 * GENERATED from templates/mealy.h.in -- do not edit.
 * Machine: vending
 */

#ifndef TRANSMOGRIFIER_MEALY_H
#define TRANSMOGRIFIER_MEALY_H

#ifdef __cplusplus
extern "C" {
#endif

typedef unsigned long long mealy_state_t;  /* 0..MEALY_NSTATES-1, or the sink */
typedef unsigned long long mealy_symbol_t; /* 0..MEALY_NSYMS-1 */
typedef unsigned long long mealy_output_t; /* 0..MEALY_NOUTS-1, or the sink */
typedef const mealy_symbol_t *mealy_word_t;

#define MEALY_NSTATES 6ULL
#define MEALY_NSYMS   4ULL
#define MEALY_NOUTS   11ULL

/** Returned by delta, and written through *out, when either index is out of range. */
#define MEALY_SINK    MEALY_NSTATES
#define MEALY_OUT_SINK MEALY_NOUTS

/** Flat size of a state/symbol-indexed table, in elements. */
#define MEALY_TABLE_LEN         (MEALY_NSTATES * MEALY_NSYMS)
/** Row-major index of (q, a) within either table. */
#define MEALY_TABLE_INDEX(q, a) ((q) * MEALY_NSYMS + (a))

/* ---- Input symbols, in Sigma.enum order ---- */
typedef enum {
    SYM_N = 0ULL, /* "n" */
    SYM_D = 1ULL, /* "d" */
    SYM_Q = 2ULL, /* "q" */
    SYM_R = 3ULL, /* "r" */
    SYM_COUNT = 4ULL /* |Sigma|; delta's out-of-range threshold */
} input_sym_t;

/* ---- Output symbols, in O.enum order ---- */
typedef enum {
    OUT__ = 0ULL, /* "-" */
    OUT_VEND = 1ULL, /* "VEND" */
    OUT_VEND_5 = 2ULL, /* "VEND+5" */
    OUT_VEND_10 = 3ULL, /* "VEND+10" */
    OUT_VEND_15 = 4ULL, /* "VEND+15" */
    OUT_VEND_20 = 5ULL, /* "VEND+20" */
    OUT_BACK_5 = 6ULL, /* "BACK 5" */
    OUT_BACK_10 = 7ULL, /* "BACK 10" */
    OUT_BACK_15 = 8ULL, /* "BACK 15" */
    OUT_BACK_20 = 9ULL, /* "BACK 20" */
    OUT_BACK_25 = 10ULL, /* "BACK 25" */
    OUT_COUNT = 11ULL /* |O|; accept_entry's out-of-range fallback */
} output_sym_t;

/* ---- Emitted globals (read-only) ---- */

/** table[q * MEALY_NSYMS + a]: the index of delta(q, a)'s next state. */
extern const mealy_state_t table[MEALY_TABLE_LEN];
/** otable[q * MEALY_NSYMS + a]: index of output(q, a) in O.enum. */
extern const mealy_output_t otable[MEALY_TABLE_LEN];
/** Index of the initial state. */
extern const mealy_state_t q0;

/* ---- Functions ---- */

/**
 * Transition and output: delta(q, a, out).
 * In range (q < MEALY_NSTATES, a < MEALY_NSYMS): writes the output symbol's
 * index through *out and returns the successor state's index.
 * Out of range: writes MEALY_OUT_SINK through *out and returns MEALY_SINK.
 * Verified: compile_delta_correct, compile_delta_sink.
 */
extern mealy_state_t delta(mealy_state_t q, mealy_symbol_t a, mealy_output_t *out);

/**
 * Run from q0 over w, writing len output indices into the caller-supplied
 * buffer out.
 * Verified: compile_run_correct.
 */
extern void run(mealy_word_t w, unsigned long long len, mealy_output_t *out);

#ifdef __cplusplus
}
#endif

#endif /* TRANSMOGRIFIER_MEALY_H */
