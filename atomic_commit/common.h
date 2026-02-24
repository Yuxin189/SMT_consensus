#ifndef COMMON_H
#define COMMON_H

#include <stdbool.h>
#include "config.h"

/* Runtime 3^NUM_NODES, set by main at startup, shared by all modules */
extern int g_num_patterns;

/* One counter-example: init vote (0=abort, 1=commit), crash_send, crash_after, loss */
typedef struct {
    int init[NUM_NODES];                                    /* 0=abort, 1=commit */
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
    double vars_mk;
    double vars_add;
    double trace;
    double agree_validity;
    double env;
    double loss;
    double violation;
} timing_t;

/* Generate INPUT_PATTERNS like Python itertools.product([0,1,2], repeat=NUM_NODES) */
void gen_input_patterns(int *patterns);

/* alive[r][i] = node i alive at start of round r+1 */
void compute_alive_from_crash_after(const bool crash_after[NUM_ROUNDS][NUM_NODES], bool alive[NUM_ROUNDS + 1][NUM_NODES]);

int counter_example_equal(const counter_example_t *a, const counter_example_t *b);

#endif /* COMMON_H */
