#ifndef COMMON_H
#define COMMON_H

#include <stdbool.h>
#include "config.h"

/* Runtime 5^NUM_NODES (recv: 0,1,2,3,4=missing), set by main at startup */
extern int g_num_patterns;

/* States (match Python atomic_commit.py): 0=Abort, 1=Commit, 2=DoNothing_Zero, 3=DoNothing_One,
 * 4=Lost/Missing, 5=LocalAbort, 6=LocalCommit. Init uses 0/1 for LocalAbort/LocalCommit. */
#define STATE_ABORT 0
#define STATE_COMMIT 1
#define STATE_DONOTHING_ZERO 2
#define STATE_DONOTHING_ONE 3
#define STATE_MISSING 4   /* recv_vec: 4=missing; Lost=4 for crashed nodes */

/* One counter-example: init (0=LocalAbort, 1=LocalCommit), crash_send, crash_after, loss */
typedef struct {
    int init[NUM_NODES];                                    /* 0=LocalAbort, 1=LocalCommit */
    bool crash_send[NUM_ROUNDS][NUM_NODES];                /* crash during send in round r */
    bool crash_after[NUM_ROUNDS][NUM_NODES];               /* crash after round r */
    bool loss[NUM_ROUNDS][NUM_NODES][NUM_NODES];           /* loss[r][src][dst]=true means delivered */
} counter_example_t;

/* Protocol: SM table, sm[round * g_num_patterns + pattern_idx] = 0,1,2,3 (Abort,Commit,DoNothing_Zero,DoNothing_One) */
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

/* Generate INPUT_PATTERNS: product([0,1,2,3,4], repeat=NUM_NODES), 4=missing */
void gen_input_patterns(int *patterns);

/* alive[r][i] = node i alive at start of round r+1 */
void compute_alive_from_crash_after(const bool crash_after[NUM_ROUNDS][NUM_NODES], bool alive[NUM_ROUNDS + 1][NUM_NODES]);

int counter_example_equal(const counter_example_t *a, const counter_example_t *b);

#endif /* COMMON_H */
