/* nfa.h -- interface to an NFA compiled to Clight by Transmogrifier.
 *
 * GENERATED from include/nfa.h.in -- do not edit.
 * Machine: secondlast
 */

#ifndef TRANSMOGRIFIER_NFA_H
#define TRANSMOGRIFIER_NFA_H

#ifdef __cplusplus
extern "C" {
#endif

#define NFA_NSTATES 3ULL
#define NFA_NSYMS   2ULL

/** Words per set: ceil(NFA_NSTATES / 64), at least 1. */
#define NFA_NWORDS  1ULL

typedef unsigned long long nfa_state_t;  /* 0..NFA_NSTATES-1 */
typedef unsigned long long nfa_symbol_t; /* 0..NFA_NSYMS-1 */
typedef nfa_symbol_t *nfa_word_t;

/** A set of states, as NFA_NWORDS words. */
typedef nfa_state_t nfa_set_t[NFA_NWORDS];

/** Bit (i % 64) of word (i / 64). */
#define NFA_SET_WORD(i)   ((i) / 64ULL)
#define NFA_SET_BIT(i)    (1ULL << ((i) % 64ULL))
#define NFA_SET_MEMBER(s, i) (((s)[NFA_SET_WORD(i)] & NFA_SET_BIT(i)) != 0ULL)

#define NFA_TABLE_LEN (NFA_NSTATES * NFA_NSYMS * NFA_NWORDS)
/** Word j of row (q, a) within the transition table. */
#define NFA_TABLE_INDEX(q, a, j) (((q) * NFA_NSYMS + (a)) * NFA_NWORDS + (j))

/* ---- Input symbols, in Sigma.enum order ---- */
typedef enum {
    SYM_A = 0ULL, /* "a" */
    SYM_B = 1ULL, /* "b" */
    SYM_COUNT = 2ULL /* |Sigma|; step's out-of-range threshold */
} nfa_input_sym_t;

/* ---- Emitted globals (read-only) ---- */

/** Row (q, a) is the NFA_NWORDS-word bitmap of delta(q, a). */
extern const nfa_state_t table[NFA_TABLE_LEN];
/** The initial set. */
extern const nfa_state_t init[NFA_NWORDS];
/** The accepting set; a run accepts iff its final set intersects this. */
extern const nfa_state_t final[NFA_NWORDS];

/* ---- Functions ---- */

/**
 * step(cur, a, next): next := the union of the a-rows of every state in cur.
 *
 * cur and next must not alias: the body zeroes next before reading the rows.
 * An out-of-range symbol leaves next empty.
 *
 * Verified: compile_step_correct (theories/transparency/nfaproofs.v).
 */
extern void step(nfa_state_t *cur, nfa_symbol_t a, nfa_state_t *next);

/**
 * accept(cur): whether cur intersects the accepting set.
 *
 * Verified: compile_accept_correct.
 */
extern _Bool accept(nfa_state_t *cur);

/**
 * run(w, len, out): out := the set reached from init after consuming w.
 *
 * Returns the reached set of states.
 *
 * w must hold len readable elements; out must have room for NFA_NWORDS words.
 *
 * Verified: compile_run_correct.
 */
extern void run(nfa_word_t w, unsigned long long len, nfa_state_t *out);

/** Whether the NFA accepts w. */
static inline int nfa_accepts(nfa_word_t w, unsigned long long len)
{
    nfa_set_t out;
    run(w, len, out);
    return accept(out);
}

#ifdef __cplusplus
}
#endif

#endif /* TRANSMOGRIFIER_NFA_H */
