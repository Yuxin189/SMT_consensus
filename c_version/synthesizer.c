#include "synthesizer.h"
#include "system_model.h"
#include <stdio.h>
#include <stdlib.h>
#include <time.h>

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec / 1e9;
}

bool synthesize(Z3_context ctx, const counter_example_t *counter_examples, int num_cex,
                const int patterns[][NUM_NODES], protocol_t *protocol, timing_t *timing) {
    Z3_solver s = Z3_mk_solver(ctx);
    Z3_solver_inc_ref(ctx, s);
    double t_start = now();

    Z3_ast *sm_vars = (Z3_ast *)malloc((size_t)NUM_ROUNDS * NUM_PATTERNS * sizeof(Z3_ast));
    Z3_sort int_sort = Z3_mk_int_sort(ctx);
    Z3_ast zero = Z3_mk_int(ctx, 0, int_sort);
    Z3_ast one = Z3_mk_int(ctx, 1, int_sort);

    double t0 = now();
    for (int r = 0; r < NUM_ROUNDS; r++) {
        for (int p = 0; p < NUM_PATTERNS; p++) {
            char name[64];
            snprintf(name, sizeof(name), "SM_R%d_P%d", r + 1, p);
            sm_vars[r * NUM_PATTERNS + p] = Z3_mk_const(ctx, Z3_mk_string_symbol(ctx, name), int_sort);
            Z3_ast or_args[2] = {
                Z3_mk_eq(ctx, sm_vars[r * NUM_PATTERNS + p], zero),
                Z3_mk_eq(ctx, sm_vars[r * NUM_PATTERNS + p], one)
            };
            Z3_solver_assert(ctx, s, Z3_mk_or(ctx, 2, or_args));
        }
    }
    double t_vars = now() - t0;

    double t_cex_start = now();
    for (int idx = 0; idx < num_cex; idx++) {
        const counter_example_t *ce = &counter_examples[idx];
        bool alive[NUM_ROUNDS + 1][NUM_NODES];
        compute_alive_from_crash_after(ce->crash_after, alive);
        char suffix[32];
        snprintf(suffix, sizeof(suffix), "ce%d", idx);
        Z3_ast S[NUM_ROUNDS + 1][NUM_NODES];
        build_trace_concrete(ctx, s, sm_vars, ce->init, alive, ce->loss, patterns, suffix, S);

        for (int i = 0; i < NUM_NODES; i++) {
            for (int j = i + 1; j < NUM_NODES; j++) {
                Z3_ast dec_i = alive[NUM_ROUNDS - 1][i] ? Z3_mk_true(ctx) : Z3_mk_false(ctx);
                Z3_ast dec_j = alive[NUM_ROUNDS - 1][j] ? Z3_mk_true(ctx) : Z3_mk_false(ctx);
                Z3_ast dec_both = Z3_mk_and(ctx, 2, (Z3_ast[]){dec_i, dec_j});
                Z3_ast agree = Z3_mk_eq(ctx, S[NUM_ROUNDS][i], S[NUM_ROUNDS][j]);
                Z3_solver_assert(ctx, s, Z3_mk_implies(ctx, dec_both, agree));
            }
        }
        int all_zero = 1, all_one = 1;
        for (int i = 0; i < NUM_NODES; i++) {
            if (ce->init[i] != 0) all_zero = 0;
            if (ce->init[i] != 1) all_one = 0;
        }
        if (all_zero) {
            for (int i = 0; i < NUM_NODES; i++) {
                Z3_ast dec_i = alive[NUM_ROUNDS - 1][i] ? Z3_mk_true(ctx) : Z3_mk_false(ctx);
                Z3_solver_assert(ctx, s, Z3_mk_implies(ctx, dec_i, Z3_mk_eq(ctx, S[NUM_ROUNDS][i], zero)));
            }
        }
        if (all_one) {
            for (int i = 0; i < NUM_NODES; i++) {
                Z3_ast dec_i = alive[NUM_ROUNDS - 1][i] ? Z3_mk_true(ctx) : Z3_mk_false(ctx);
                Z3_solver_assert(ctx, s, Z3_mk_implies(ctx, dec_i, Z3_mk_eq(ctx, S[NUM_ROUNDS][i], one)));
            }
        }
    }
    double t_cex = now() - t_cex_start;

    double t_solve_start = now();
    Z3_lbool result = Z3_solver_check(ctx, s);
    double t_solve = now() - t_solve_start;

    if (result != Z3_L_TRUE) {
        timing->gen = t_vars + t_cex;
        timing->solve = t_solve;
        timing->model = 0;
        timing->total = now() - t_start;
        Z3_solver_dec_ref(ctx, s);
        free(sm_vars);
        return false;
    }

    Z3_model m = Z3_solver_get_model(ctx, s);
    Z3_model_inc_ref(ctx, m);
    double t_model_start = now();
    for (int r = 0; r < NUM_ROUNDS; r++) {
        for (int p = 0; p < NUM_PATTERNS; p++) {
            Z3_ast val;
            if (!Z3_model_eval(ctx, m, sm_vars[r * NUM_PATTERNS + p], 1, &val)) continue;
            int n;
            if (Z3_get_numeral_int(ctx, val, &n))
                protocol->sm[r][p] = n;
        }
    }
    double t_model = now() - t_model_start;
    Z3_model_dec_ref(ctx, m);
    Z3_solver_dec_ref(ctx, s);
    free(sm_vars);

    timing->gen = t_vars + t_cex;
    timing->solve = t_solve;
    timing->model = t_model;
    timing->total = now() - t_start;
    return true;
}
