/* dfa.h -- interface to a DFA compiled to Clight by Transmogrifier.
 *
 * GENERATED from templates/dfa.h.in -- do not edit.
 * Machine: alternating
 */

#ifndef TRANSMOGRIFIER_DFA_H
#define TRANSMOGRIFIER_DFA_H

#ifdef __cplusplus
extern "C" {
#endif

typedef unsigned long long dfa_state_t;   /* 0..DFA_NSTATES-1, or DFA_SINK */
typedef unsigned long long dfa_symbol_t;  /* 0..DFA_NSYMS-1 */
typedef unsigned long long dfa_output_t;  /* 0..1; see the enum below */
typedef dfa_symbol_t *dfa_word_t;

#define DFA_NSTATES 4ULL
#define DFA_NSYMS   2ULL
#define DFA_SINK    DFA_NSTATES

#define DFA_TABLE_LEN         (DFA_NSTATES * DFA_NSYMS)
#define DFA_TABLE_INDEX(q, a) ((q) * DFA_NSYMS + (a))

/* ---- Input symbols, in Sigma.enum order ---- */
typedef enum {
    SYM_0 = 0ULL, /* "0" */
    SYM_1 = 1ULL, /* "1" */
    SYM_COUNT = 2ULL /* |Sigma|; delta's out-of-range threshold */
} dfa_input_sym_t;

/* ---- The bool output alphabet ----
 *
 * accept returns an index into O.enum, and for a DFA that enum is
 *
 *     Definition enum := [true; false].      (* theories/compiler/dfa.v *)
 *
 * so accepting is 0 and rejecting is 1. This inverts the C convention:
 * `if (accept(q))` is BACKWARDS. Use DFA_IS_ACCEPTING or the wrappers below.
 */
typedef enum {
    DFA_TRUE = 0ULL, /* "true" */
    DFA_FALSE = 1ULL, /* "false" */
    DFA_COUNT = 2ULL /* |O|; accept_entry's out-of-range fallback */
} dfa_bool;

#define DFA_ACCEPT_INDEX 0ULL
#define DFA_REJECT_INDEX 1ULL
#define DFA_IS_ACCEPTING(o) ((o) == DFA_ACCEPT_INDEX)

/* ---- Emitted globals (read-only) ---- */
extern const dfa_state_t  table[DFA_TABLE_LEN];
extern const dfa_output_t atable[DFA_NSTATES];
extern const dfa_state_t  q0;

/* ---- Functions ---- */
extern dfa_state_t  delta(dfa_state_t q, dfa_symbol_t a);
extern dfa_output_t accept(dfa_state_t q);
extern dfa_state_t  run(dfa_word_t w, unsigned long long len);

/** Whether q is accepting. Only q < DFA_NSTATES is proved
 *  (compile_accept_correct assumes a valid state index). */
static inline int dfa_state_accepts(dfa_state_t q)
{
    return DFA_IS_ACCEPTING(accept(q));
}

/** Whether the DFA accepts w. This is the composition the correctness theorems
 *  are about: compile_run_correct lands on the right state, and
 *  compile_accept_correct reports its output. */
static inline int dfa_accepts(dfa_word_t w, unsigned long long len)
{
    return dfa_state_accepts(run(w, len));
}

#ifdef __cplusplus
}
#endif

#endif /* TRANSMOGRIFIER_DFA_H */
