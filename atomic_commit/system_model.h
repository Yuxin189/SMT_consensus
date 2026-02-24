#ifndef SYSTEM_MODEL_H
#define SYSTEM_MODEL_H

#include <z3.h>
#include "config.h"
#include "common.h"

/* Build execution trace for synthesizer: concrete init/alive/loss, symbolic sm_vars. */
void build_trace_concrete(Z3_context ctx, Z3_solver s, Z3_ast *sm_vars,
                          const int *init, const bool alive[NUM_ROUNDS + 1][NUM_NODES],
                          const bool loss[NUM_ROUNDS][NUM_NODES][NUM_NODES],
                          const int *patterns, const char *suffix,
                          Z3_ast S[NUM_ROUNDS + 1][NUM_NODES]);

/* Build execution trace for verifier: symbolic Init/Alive/Loss, concrete sm_logic. */
void build_trace_symbolic(Z3_context ctx, Z3_solver s, const int *sm_logic,
                          Z3_ast *Init, Z3_ast Alive[NUM_ROUNDS + 1][NUM_NODES],
                          Z3_ast Loss[NUM_ROUNDS][NUM_NODES][NUM_NODES],
                          const int *patterns, const char *suffix,
                          Z3_ast S[NUM_ROUNDS + 1][NUM_NODES]);

#endif /* SYSTEM_MODEL_H */
