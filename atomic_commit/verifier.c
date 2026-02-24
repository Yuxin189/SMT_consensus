#include "verifier.h"
#include "system_model.h"
#include <stdio.h>
#include <stdlib.h>
#include <time.h>

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec / 1e9;
}

static int is_true(Z3_context ctx, Z3_model m, Z3_ast a) {
    Z3_ast val;
    if (!Z3_model_eval(ctx, m, a, 1, &val)) return 0;
    return Z3_get_bool_value(ctx, val) == Z3_L_TRUE;
}

int verify(Z3_context ctx, const protocol_t *protocol, const int *patterns,
            counter_example_t *cex, timing_t *timing) {
    Z3_solver s = Z3_mk_solver(ctx);
    Z3_solver_inc_ref(ctx, s);
    double t_start = now();
    double t0;

    Z3_sort int_sort = Z3_mk_int_sort(ctx);
    Z3_sort bool_sort = Z3_mk_bool_sort(ctx);

    t0 = now();
    Z3_ast Init[NUM_NODES];
    for (int i = 0; i < NUM_NODES; i++) {
        char name[32];
        snprintf(name, sizeof(name), "Init_%d", i);
        Init[i] = Z3_mk_const(ctx, Z3_mk_string_symbol(ctx, name), int_sort);
        Z3_ast args[2] = {
            Z3_mk_eq(ctx, Init[i], Z3_mk_int(ctx, 0, int_sort)),
            Z3_mk_eq(ctx, Init[i], Z3_mk_int(ctx, 1, int_sort))
        };
        Z3_solver_assert(ctx, s, Z3_mk_or(ctx, 2, args));
    }

    Z3_ast Alive[NUM_ROUNDS + 1][NUM_NODES];
    for (int r = 0; r <= NUM_ROUNDS; r++) {
        for (int i = 0; i < NUM_NODES; i++) {
            char name[64];
            snprintf(name, sizeof(name), "Alive_r%d_n%d", r, i);
            Alive[r][i] = Z3_mk_const(ctx, Z3_mk_string_symbol(ctx, name), bool_sort);
        }
    }
    for (int i = 0; i < NUM_NODES; i++)
        Z3_solver_assert(ctx, s, Z3_mk_eq(ctx, Alive[0][i], Z3_mk_true(ctx)));

    Z3_ast CrashSend[NUM_ROUNDS][NUM_NODES];
    Z3_ast CrashAfter[NUM_ROUNDS][NUM_NODES];
    for (int r = 0; r < NUM_ROUNDS; r++) {
        for (int i = 0; i < NUM_NODES; i++) {
            char name[64];
            snprintf(name, sizeof(name), "CrashSend_r%d_n%d", r, i);
            CrashSend[r][i] = Z3_mk_const(ctx, Z3_mk_string_symbol(ctx, name), bool_sort);
            snprintf(name, sizeof(name), "CrashAfter_r%d_n%d", r, i);
            CrashAfter[r][i] = Z3_mk_const(ctx, Z3_mk_string_symbol(ctx, name), bool_sort);
        }
    }

    for (int r = 0; r < NUM_ROUNDS; r++) {
        for (int i = 0; i < NUM_NODES; i++) {
            Z3_ast args[2] = {Alive[r][i], Z3_mk_not(ctx, CrashAfter[r][i])};
            Z3_solver_assert(ctx, s, Z3_mk_eq(ctx, Alive[r + 1][i], Z3_mk_and(ctx, 2, args)));
            Z3_ast dead = Z3_mk_not(ctx, Alive[r][i]);
            Z3_ast no_crash[2] = {Z3_mk_not(ctx, CrashSend[r][i]), Z3_mk_not(ctx, CrashAfter[r][i])};
            Z3_solver_assert(ctx, s, Z3_mk_implies(ctx, dead, Z3_mk_and(ctx, 2, no_crash)));
        }
    }
    for (int r = 0; r < NUM_ROUNDS; r++) {
        for (int i = 0; i < NUM_NODES; i++)
            Z3_solver_assert(ctx, s, Z3_mk_implies(ctx, CrashSend[r][i], CrashAfter[r][i]));
    }
    double t_env = now() - t0;

    t0 = now();
    Z3_ast Loss[NUM_ROUNDS][NUM_NODES][NUM_NODES];
    for (int r = 0; r < NUM_ROUNDS; r++) {
        for (int src = 0; src < NUM_NODES; src++) {
            for (int dst = 0; dst < NUM_NODES; dst++) {
                char name[64];
                snprintf(name, sizeof(name), "Loss_r%d_%d_%d", r, src, dst);
                Loss[r][src][dst] = Z3_mk_const(ctx, Z3_mk_string_symbol(ctx, name), bool_sort);
            }
        }
    }
    for (int r = 0; r < NUM_ROUNDS; r++) {
        for (int src = 0; src < NUM_NODES; src++) {
            Z3_ast alive_src = Alive[r][src];
            for (int dst = 0; dst < NUM_NODES; dst++) {
                Z3_solver_assert(ctx, s, Z3_mk_implies(ctx, Z3_mk_not(ctx, alive_src),
                    Z3_mk_eq(ctx, Loss[r][src][dst], Z3_mk_false(ctx))));
            }
            for (int dst = 0; dst < NUM_NODES; dst++) {
                Z3_ast args[2] = {alive_src, Z3_mk_not(ctx, CrashSend[r][src])};
                Z3_solver_assert(ctx, s, Z3_mk_implies(ctx, Z3_mk_and(ctx, 2, args),
                    Z3_mk_eq(ctx, Loss[r][src][dst], Z3_mk_true(ctx))));
            }
            for (int dst = 0; dst < NUM_NODES; dst++) {
                Z3_ast args[2] = {alive_src, Z3_mk_eq(ctx, Loss[r][src][dst], Z3_mk_false(ctx))};
                Z3_solver_assert(ctx, s, Z3_mk_implies(ctx, Z3_mk_and(ctx, 2, args), CrashSend[r][src]));
            }
        }
    }
    for (int r = 0; r < NUM_ROUNDS; r++) {
        for (int i = 0; i < NUM_NODES; i++)
            Z3_solver_assert(ctx, s, Z3_mk_implies(ctx, Alive[r][i], Z3_mk_eq(ctx, Loss[r][i][i], Z3_mk_true(ctx))));
    }
    double t_loss = now() - t0;

    t0 = now();
    Z3_ast S[NUM_ROUNDS + 1][NUM_NODES];
    build_trace_symbolic(ctx, s, protocol->sm, Init, Alive, Loss, patterns, "verify", S);
    double t_trace = now() - t0;

    t0 = now();
    /* Violations: agreement + validity (Atomic Commit) */
    int nviol = 0;
    int max_viol = NUM_NODES * (NUM_NODES - 1) / 2 + NUM_NODES * 2;
    Z3_ast *violations = (Z3_ast *)malloc((size_t)max_viol * sizeof(Z3_ast));
    for (int i = 0; i < NUM_NODES; i++) {
        for (int j = i + 1; j < NUM_NODES; j++) {
            Z3_ast args[3] = {
                Alive[NUM_ROUNDS - 1][i],
                Alive[NUM_ROUNDS - 1][j],
                Z3_mk_not(ctx, Z3_mk_eq(ctx, S[NUM_ROUNDS][i], S[NUM_ROUNDS][j]))
            };
            violations[nviol++] = Z3_mk_and(ctx, 3, args);
        }
    }
    Z3_ast all_abort = Z3_mk_true(ctx);
    Z3_ast all_commit = Z3_mk_true(ctx);
    for (int i = 0; i < NUM_NODES; i++) {
        all_abort = Z3_mk_and(ctx, 2, (Z3_ast[]){all_abort, Z3_mk_eq(ctx, Init[i], Z3_mk_int(ctx, 0, int_sort))});
        all_commit = Z3_mk_and(ctx, 2, (Z3_ast[]){all_commit, Z3_mk_eq(ctx, Init[i], Z3_mk_int(ctx, 1, int_sort))});
    }
    for (int i = 0; i < NUM_NODES; i++) {
        Z3_ast dec_i = Alive[NUM_ROUNDS - 1][i];
        Z3_ast args0[3] = {all_abort, dec_i, Z3_mk_not(ctx, Z3_mk_eq(ctx, S[NUM_ROUNDS][i], Z3_mk_int(ctx, 0, int_sort)))};
        violations[nviol++] = Z3_mk_and(ctx, 3, args0);
        Z3_ast args1[3] = {all_commit, dec_i, Z3_mk_not(ctx, Z3_mk_eq(ctx, S[NUM_ROUNDS][i], Z3_mk_int(ctx, 1, int_sort)))};
        violations[nviol++] = Z3_mk_and(ctx, 3, args1);
    }
    Z3_solver_assert(ctx, s, Z3_mk_or(ctx, nviol, violations));
    Z3_ast survivors[NUM_NODES];
    for (int i = 0; i < NUM_NODES; i++)
        survivors[i] = Alive[NUM_ROUNDS][i];
    Z3_solver_assert(ctx, s, Z3_mk_or(ctx, NUM_NODES, survivors));
    free(violations);
    double t_violation = now() - t0;

    double t_gen = now() - t_start;
    double t_before_solve = now();
    Z3_lbool result = Z3_solver_check(ctx, s);
    double t_solve = now() - t_before_solve;

    if (result == Z3_L_FALSE) {
        timing->gen = t_gen;
        timing->solve = t_solve;
        timing->model = 0;
        timing->total = now() - t_start;
        timing->env = t_env;
        timing->loss = t_loss;
        timing->trace = t_trace;
        timing->violation = t_violation;
        Z3_solver_dec_ref(ctx, s);
        return 2; /* verified */
    }
    if (result == Z3_L_UNDEF) {
        timing->gen = t_gen;
        timing->solve = t_solve;
        timing->model = 0;
        timing->total = now() - t_start;
        timing->env = t_env;
        timing->loss = t_loss;
        timing->trace = t_trace;
        timing->violation = t_violation;
        Z3_solver_dec_ref(ctx, s);
        return 0; /* unknown */
    }

    Z3_model m = Z3_solver_get_model(ctx, s);
    Z3_model_inc_ref(ctx, m);
    double t_model_start = now();
    for (int i = 0; i < NUM_NODES; i++) {
        Z3_ast val;
        if (Z3_model_eval(ctx, m, Init[i], 1, &val)) {
            int n;
            if (Z3_get_numeral_int(ctx, val, &n)) cex->init[i] = n;
        }
    }
    for (int r = 0; r < NUM_ROUNDS; r++) {
        for (int i = 0; i < NUM_NODES; i++) {
            cex->crash_send[r][i] = is_true(ctx, m, CrashSend[r][i]);
            cex->crash_after[r][i] = is_true(ctx, m, CrashAfter[r][i]);
        }
    }
    for (int r = 0; r < NUM_ROUNDS; r++) {
        for (int src = 0; src < NUM_NODES; src++) {
            for (int dst = 0; dst < NUM_NODES; dst++)
                cex->loss[r][src][dst] = is_true(ctx, m, Loss[r][src][dst]);
        }
    }
    double t_model = now() - t_model_start;
    Z3_model_dec_ref(ctx, m);
    Z3_solver_dec_ref(ctx, s);

    timing->gen = t_gen;
    timing->solve = t_solve;
    timing->model = t_model;
    timing->total = now() - t_start;
    timing->env = t_env;
    timing->loss = t_loss;
    timing->trace = t_trace;
    timing->violation = t_violation;
    return 1; /* sat = cex found */
}
