#include "system_model.h"
#include <stdio.h>
#include <stdlib.h>

static Z3_ast mk_int(Z3_context ctx, int v) {
    Z3_sort sort = Z3_mk_int_sort(ctx);
    return Z3_mk_int(ctx, v, sort);
}

/* Pattern-matching ITE: default last pattern, then iterate backward (same as Python) */
static Z3_ast mk_pattern_ite(Z3_context ctx, const int *patterns, Z3_ast *recv_vec,
                             const Z3_ast *round_rules) {
    Z3_ast nested = round_rules[g_num_patterns - 1];
    for (int p_idx = g_num_patterns - 2; p_idx >= 0; p_idx--) {
        Z3_ast match = Z3_mk_true(ctx);
        for (int k = 0; k < NUM_NODES; k++) {
            Z3_ast eq = Z3_mk_eq(ctx, recv_vec[k], mk_int(ctx, patterns[p_idx * NUM_NODES + k]));
            match = Z3_mk_and(ctx, 2, (Z3_ast[]){match, eq});
        }
        nested = Z3_mk_ite(ctx, match, round_rules[p_idx], nested);
    }
    return nested;
}

void build_trace_concrete(Z3_context ctx, Z3_solver s, Z3_ast *sm_vars,
                          const int *init, const bool alive[NUM_ROUNDS + 1][NUM_NODES],
                          const bool loss[NUM_ROUNDS][NUM_NODES][NUM_NODES],
                          const int *patterns, const char *suffix,
                          Z3_ast S[NUM_ROUNDS + 1][NUM_NODES]) {
    Z3_ast two = mk_int(ctx, 2);
    Z3_ast init_eqs[NUM_NODES];
    for (int i = 0; i < NUM_NODES; i++) {
        char name[128];
        snprintf(name, sizeof(name), "S_r0_n%d_%s", i, suffix);
        S[0][i] = Z3_mk_const(ctx, Z3_mk_string_symbol(ctx, name), Z3_mk_int_sort(ctx));
        init_eqs[i] = Z3_mk_eq(ctx, S[0][i], mk_int(ctx, init[i]));
    }
    Z3_solver_assert(ctx, s, NUM_NODES == 1 ? init_eqs[0] : Z3_mk_and(ctx, NUM_NODES, init_eqs));
    for (int r = 1; r <= NUM_ROUNDS; r++) {
        int r1 = r - 1;
        Z3_ast round_eqs[NUM_NODES];
        for (int i = 0; i < NUM_NODES; i++) {
            Z3_ast recv_vec[NUM_NODES];
            for (int sender = 0; sender < NUM_NODES; sender++) {
                if (sender == i) {
                    recv_vec[sender] = alive[r1][i] ? S[r1][i] : two;
                } else {
                    int delivered = alive[r1][sender] && loss[r1][sender][i];
                    recv_vec[sender] = delivered ? S[r1][sender] : two;
                }
            }
            Z3_ast *round_rules = sm_vars + r1 * g_num_patterns;
            Z3_ast new_state = mk_pattern_ite(ctx, patterns, recv_vec, round_rules);
            Z3_ast eq_rhs = alive[r1][i] ? new_state : S[r1][i];
            char name[128];
            snprintf(name, sizeof(name), "S_r%d_n%d_%s", r, i, suffix);
            S[r][i] = Z3_mk_const(ctx, Z3_mk_string_symbol(ctx, name), Z3_mk_int_sort(ctx));
            round_eqs[i] = Z3_mk_eq(ctx, S[r][i], eq_rhs);
        }
        Z3_solver_assert(ctx, s, NUM_NODES == 1 ? round_eqs[0] : Z3_mk_and(ctx, NUM_NODES, round_eqs));
    }
}

void build_trace_symbolic(Z3_context ctx, Z3_solver s, const int *sm_logic,
                          Z3_ast *Init, Z3_ast Alive[NUM_ROUNDS + 1][NUM_NODES],
                          Z3_ast Loss[NUM_ROUNDS][NUM_NODES][NUM_NODES],
                          const int *patterns, const char *suffix,
                          Z3_ast S[NUM_ROUNDS + 1][NUM_NODES]) {
    Z3_sort int_sort = Z3_mk_int_sort(ctx);
    Z3_ast two = mk_int(ctx, 2);
    for (int i = 0; i < NUM_NODES; i++) {
        char name[128];
        snprintf(name, sizeof(name), "S_r0_n%d_%s", i, suffix);
        S[0][i] = Z3_mk_const(ctx, Z3_mk_string_symbol(ctx, name), int_sort);
        Z3_solver_assert(ctx, s, Z3_mk_eq(ctx, S[0][i], Init[i]));
    }
    for (int r = 1; r <= NUM_ROUNDS; r++) {
        int r1 = r - 1;
        for (int i = 0; i < NUM_NODES; i++) {
            Z3_ast recv_vec[NUM_NODES];
            for (int sender = 0; sender < NUM_NODES; sender++) {
                if (sender == i) {
                    recv_vec[sender] = Z3_mk_ite(ctx, Alive[r1][i], S[r1][i], two);
                } else {
                    Z3_ast delivered = Z3_mk_and(ctx, 2, (Z3_ast[]){Alive[r1][sender], Loss[r1][sender][i]});
                    recv_vec[sender] = Z3_mk_ite(ctx, delivered, S[r1][sender], two);
                }
            }
            Z3_ast *round_rules = (Z3_ast *)malloc((size_t)g_num_patterns * sizeof(Z3_ast));
            for (int p = 0; p < g_num_patterns; p++)
                round_rules[p] = mk_int(ctx, sm_logic[r1 * g_num_patterns + p]);
            Z3_ast new_state = mk_pattern_ite(ctx, patterns, recv_vec, round_rules);
            Z3_ast eq_rhs = Z3_mk_ite(ctx, Alive[r1][i], new_state, S[r1][i]);
            free(round_rules);
            char name[128];
            snprintf(name, sizeof(name), "S_r%d_n%d_%s", r, i, suffix);
            S[r][i] = Z3_mk_const(ctx, Z3_mk_string_symbol(ctx, name), int_sort);
            Z3_solver_assert(ctx, s, Z3_mk_eq(ctx, S[r][i], eq_rhs));
        }
    }
}
