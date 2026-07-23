/* mealy.h -- interface to a Mealy machine compiled to Clight by Transmogrifier.
 *
 * GENERATED from templates/mealy.h.in -- do not edit.
 * Machine: session
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

#define MEALY_NSTATES 4ULL
#define MEALY_NSYMS   5ULL
#define MEALY_NOUTS   5ULL

/** Returned by delta, and written through *out, when either index is out of range. */
#define MEALY_SINK    MEALY_NSTATES
#define MEALY_OUT_SINK MEALY_NOUTS

/** Flat size of a state/symbol-indexed table, in elements. */
#define MEALY_TABLE_LEN         (MEALY_NSTATES * MEALY_NSYMS)
/** Row-major index of (q, a) within either table. */
#define MEALY_TABLE_INDEX(q, a) ((q) * MEALY_NSYMS + (a))

/* ---- Input symbols, in Sigma.enum order ---- */
typedef enum {
    SYM_H = 0ULL, /* "h" */
    SYM_A = 1ULL, /* "a" */
    SYM_R = 2ULL, /* "r" */
    SYM_K = 3ULL, /* "k" */
    SYM_X = 4ULL, /* "x" */
    SYM_COUNT = 5ULL /* |Sigma|; delta's out-of-range threshold */
} input_sym_t;

/* ---- Output symbols, in O.enum order ---- */
typedef enum {
    OUT_DENY = 0ULL, /* "DENY" */
    OUT_WAIT = 1ULL, /* "WAIT" */
    OUT_PROCEED = 2ULL, /* "PROCEED" */
    OUT_GRANT = 3ULL, /* "GRANT" */
    OUT_BYE = 4ULL, /* "BYE" */
    OUT_COUNT = 5ULL /* |O|; accept_entry's out-of-range fallback */
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
