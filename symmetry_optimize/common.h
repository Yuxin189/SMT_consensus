#ifndef COMMON_H
#define COMMON_H

#include <z3.h>
#include <stdbool.h>
#include "config.h"

/* Runtime number of canonical count patterns, set by main at startup, shared by all modules */
extern int g_num_patterns;

/* One counter-example: same structure as v2 Python (init, crash_send, crash_after, loss) */
typedef struct {
    int init[NUM_NODES];                                    /* 0 or 1 */
    bool crash_send[NUM_ROUNDS][NUM_NODES];                /* crash during send in round r */
    bool crash_after[NUM_ROUNDS][NUM_NODES];               /* crash after round r */
    bool loss[NUM_ROUNDS][NUM_NODES][NUM_NODES];           /* loss[r][src][dst]=true means delivered */
} counter_example_t;

/* Protocol: canonical SM table, row-major sm[round * g_num_patterns + pattern_idx] = 0 or 1 */
typedef struct {
    int *sm;
} protocol_t;

typedef struct {
    double gen;
    double solve;
    double model;
    double total;
    double constraints_count;
    double ast_count;
    unsigned constraints;
    unsigned long long ast_nodes;
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

/* Return number of canonical (count0, count1) patterns: (NUM_NODES + 1)(NUM_NODES + 2)/2. */
int get_num_canonical_patterns(void);

/* Map (count0, count1) to canonical row-major index. Requires count0 >= 0, count1 >= 0, count0 + count1 <= NUM_NODES. */
int canonical_index_from_counts(int count0, int count1);

/* Generate canonical patterns as row-major (count0, count1) pairs. Caller allocates patterns[g_num_patterns * 2]. */
void gen_input_patterns(int *patterns);

/* alive[r][i] = node i alive at start of round r+1 (r=0..NUM_ROUNDS). Caller provides alive[NUM_ROUNDS+1][NUM_NODES]. */
void compute_alive_from_crash_after(const bool crash_after[NUM_ROUNDS][NUM_NODES], bool alive[NUM_ROUNDS + 1][NUM_NODES]);

int counter_example_equal(const counter_example_t *a, const counter_example_t *b);

/* Count unique AST nodes reachable from all formulas in an assertion vector. */
unsigned long long count_ast_nodes_in_vector(Z3_context ctx, Z3_ast_vector v);

#endif /* COMMON_H */
