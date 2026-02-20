#include "common.h"
#include <stdlib.h>
#include <string.h>

int g_num_patterns;

int counter_example_equal(const counter_example_t *a, const counter_example_t *b) {
    return memcmp(a, b, sizeof(counter_example_t)) == 0;
}

static int pow3(int n) {
    int p = 1;
    for (int i = 0; i < n; i++) p *= 3;
    return p;
}

void gen_input_patterns(int *patterns) {
    for (int p = 0; p < g_num_patterns; p++) {
        for (int k = 0; k < NUM_NODES; k++) {
            patterns[p * NUM_NODES + k] = (p / pow3(NUM_NODES - 1 - k)) % 3;
        }
    }
}

void compute_alive_from_crash_after(const bool crash_after[NUM_ROUNDS][NUM_NODES], bool alive[NUM_ROUNDS + 1][NUM_NODES]) {
    for (int i = 0; i < NUM_NODES; i++)
        alive[0][i] = true;
    for (int r = 0; r < NUM_ROUNDS; r++) {
        for (int i = 0; i < NUM_NODES; i++)
            alive[r + 1][i] = alive[r][i] && !crash_after[r][i];
    }
}
