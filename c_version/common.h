#ifndef COMMON_H
#define COMMON_H

#include <stdbool.h>
#include "config.h"

/* Runtime 3^NUM_NODES, set by main at startup, shared by all modules */
extern int g_num_patterns;

/* One counter-example: same structure as v2 Python (init, crash_send, crash_after, loss) */
typedef struct {
    int init[NUM_NODES];                                    /* 0 or 1 */
    bool crash_send[NUM_ROUNDS][NUM_NODES];                /* crash during send in round r */
    bool crash_after[NUM_ROUNDS][NUM_NODES];               /* crash after round r */
    bool loss[NUM_ROUNDS][NUM_NODES][NUM_NODES];           /* loss[r][src][dst]=true means delivered */
} counter_example_t;

/* Protocol: SM table, row-major sm[round * g_num_patterns + pattern_idx] = 0 or 1 */
typedef struct {
    int *sm;
} protocol_t;

typedef struct {
    double gen;
    double solve;
    double model;
    double total;
    /* Synthesizer breakdown (others zero when from verify) */
    double vars_mk;
    double vars_add;
    double trace;
    double agree_validity;
    /* Verifier breakdown (others zero when from synthesize) */
    double env;
    double loss;
    double violation;
} timing_t;

/* Generate INPUT_PATTERNS like Python itertools.product([0,1,2], repeat=NUM_NODES); row-major patterns[p*NUM_NODES+k]; g_num_patterns must be set first */
void gen_input_patterns(int *patterns);

/* alive[r][i] = node i alive at start of round r+1 (r=0..NUM_ROUNDS). Caller provides alive[NUM_ROUNDS+1][NUM_NODES]. */
void compute_alive_from_crash_after(const bool crash_after[NUM_ROUNDS][NUM_NODES], bool alive[NUM_ROUNDS + 1][NUM_NODES]);

int counter_example_equal(const counter_example_t *a, const counter_example_t *b);

#endif /* COMMON_H */
