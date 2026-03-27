#include "common.h"
#include <limits.h>
#include <stdlib.h>
#include <string.h>

int g_num_patterns;

int counter_example_equal(const counter_example_t *a, const counter_example_t *b) {
    return memcmp(a, b, sizeof(counter_example_t)) == 0;
}

int get_num_canonical_patterns(void) {
    return (NUM_NODES + 1) * (NUM_NODES + 2) / 2;
}

int canonical_index_from_counts(int count0, int count1) {
    int idx = 0;
    for (int c0 = 0; c0 < count0; c0++)
        idx += NUM_NODES - c0 + 1;
    return idx + count1;
}

void gen_input_patterns(int *patterns) {
    int idx = 0;
    for (int count0 = 0; count0 <= NUM_NODES; count0++) {
        for (int count1 = 0; count0 + count1 <= NUM_NODES; count1++) {
            patterns[idx * 2] = count0;
            patterns[idx * 2 + 1] = count1;
            idx++;
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

typedef struct {
    unsigned *keys;
    size_t cap;
    size_t used;
} ast_id_set_t;

static void ast_id_set_init(ast_id_set_t *set) {
    set->cap = 1024;
    set->used = 0;
    set->keys = (unsigned *)malloc(set->cap * sizeof(unsigned));
    for (size_t i = 0; i < set->cap; i++) set->keys[i] = UINT_MAX;
}

static void ast_id_set_free(ast_id_set_t *set) {
    free(set->keys);
    set->keys = NULL;
    set->cap = 0;
    set->used = 0;
}

static void ast_id_set_rehash(ast_id_set_t *set) {
    unsigned *old_keys = set->keys;
    size_t old_cap = set->cap;
    set->cap *= 2;
    set->keys = (unsigned *)malloc(set->cap * sizeof(unsigned));
    for (size_t i = 0; i < set->cap; i++) set->keys[i] = UINT_MAX;
    set->used = 0;
    for (size_t i = 0; i < old_cap; i++) {
        if (old_keys[i] != UINT_MAX) {
            size_t idx = old_keys[i] & (set->cap - 1);
            while (set->keys[idx] != UINT_MAX) idx = (idx + 1) & (set->cap - 1);
            set->keys[idx] = old_keys[i];
            set->used++;
        }
    }
    free(old_keys);
}

static int ast_id_set_insert(ast_id_set_t *set, unsigned key) {
    if ((set->used + 1) * 2 >= set->cap) ast_id_set_rehash(set);
    size_t idx = key & (set->cap - 1);
    while (set->keys[idx] != UINT_MAX) {
        if (set->keys[idx] == key) return 0;
        idx = (idx + 1) & (set->cap - 1);
    }
    set->keys[idx] = key;
    set->used++;
    return 1;
}

static unsigned long long count_ast_nodes_rec(Z3_context ctx, Z3_ast ast, ast_id_set_t *seen) {
    unsigned id = Z3_get_ast_id(ctx, ast);
    if (!ast_id_set_insert(seen, id)) return 0;

    unsigned long long total = 1;
    if (Z3_get_ast_kind(ctx, ast) == Z3_APP_AST) {
        Z3_app app = Z3_to_app(ctx, ast);
        unsigned nargs = Z3_get_app_num_args(ctx, app);
        for (unsigned i = 0; i < nargs; i++)
            total += count_ast_nodes_rec(ctx, Z3_get_app_arg(ctx, app, i), seen);
    }
    return total;
}

unsigned long long count_ast_nodes_in_vector(Z3_context ctx, Z3_ast_vector v) {
    ast_id_set_t seen;
    ast_id_set_init(&seen);

    unsigned long long total = 0;
    unsigned n = Z3_ast_vector_size(ctx, v);
    for (unsigned i = 0; i < n; i++)
        total += count_ast_nodes_rec(ctx, Z3_ast_vector_get(ctx, v, i), &seen);

    ast_id_set_free(&seen);
    return total;
}
