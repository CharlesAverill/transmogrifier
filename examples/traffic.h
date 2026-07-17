/* moore.h -- interface to a Moore machine compiled to Clight by Transmogrifier.
 *
 * GENERATED from templates/moore.h.in -- do not edit.
 * Machine: traffic
 */

#ifndef TRANSMOGRIFIER_MOORE_H
#define TRANSMOGRIFIER_MOORE_H

#ifdef __cplusplus
extern "C" {
#endif

typedef unsigned long long moore_state_t;  /* 0..MOORE_NSTATES-1, or the sink */
typedef unsigned long long moore_symbol_t; /* 0..MOORE_NSYMS-1 */
typedef unsigned long long moore_output_t; /* 0..MOORE_NOUTS-1 */
typedef const moore_symbol_t *moore_word_t;

#define MOORE_NSTATES 4ULL
#define MOORE_NSYMS   2ULL
#define MOORE_NOUTS   4ULL

/** Returned by delta when either index is out of range. */
#define MOORE_SINK    MOORE_NSTATES

/** Flat size of the transition table, in elements. */
#define MOORE_TABLE_LEN         (MOORE_NSTATES * MOORE_NSYMS)
/** Row-major index of (q, a) within the transition table. */
#define MOORE_TABLE_INDEX(q, a) ((q) * MOORE_NSYMS + (a))

/* ---- Input symbols, in Sigma.enum order ---- */
typedef enum {
    SYM_T = 0ULL, /* "t" */
    SYM_R = 1ULL, /* "r" */
    SYM_COUNT = 2ULL /* |Sigma|; delta's out-of-range threshold */
} input_sym_t;

/* ---- Output symbols, in O.enum order ---- */
typedef enum {
    OUT_RED = 0ULL, /* "RED" */
    OUT_GREEN = 1ULL, /* "GREEN" */
    OUT_YELLOW = 2ULL, /* "YELLOW" */
    OUT_RED_YELLOW = 3ULL, /* "RED+YELLOW" */
    OUT_COUNT = 4ULL /* |O|; accept_entry's out-of-range fallback */
} output_sym_t;

/* ---- Emitted globals (read-only) ---- */

/** table[q * MOORE_NSYMS + a] == delta(q, a). */
extern const moore_state_t table[MOORE_TABLE_LEN];
/** atable[q] == index of lambda(q) in O.enum. */
extern const moore_output_t atable[MOORE_NSTATES];
/** Index of the initial state. */
extern const moore_state_t q0;

/* ---- Functions ---- */

/**
 * Transition: delta(q, a).
 * In range (q < MOORE_NSTATES, a < MOORE_NSYMS): the successor's index.
 * Out of range: MOORE_SINK.
 * Verified: compile_delta_correct, compile_delta_sink.
 */
extern moore_state_t delta(moore_state_t q, moore_symbol_t a);

/**
 * Output: lambda(q). Returns the index of q's output symbol.
 */
extern moore_output_t output(moore_state_t q);

/**
 * Run from q0 over w. Equivalent to folding delta over w.
 * Verified: compile_run_correct.
 */
extern moore_state_t run(moore_word_t w, unsigned long long len);

/** The output produced by running w from q0. Not emitted -- the obvious
 *  composition, provided for convenience. */
static inline moore_output_t moore_run_output(moore_word_t w,
                                              unsigned long long len)
{
    return output(run(w, len));
}

#ifdef __cplusplus
}
#endif

#endif /* TRANSMOGRIFIER_MOORE_H */
