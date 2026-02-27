#include <stdio.h>
#include <stdlib.h>
#include <z3.h>

#include "config.h"
#include "common.h"
#include "synthesizer.h"
#include "verifier.h"

#define MAX_CEX  20000
#define MAX_ITER 8000

int main(void) {
    g_num_patterns = 1;
    for (int i = 0; i < NUM_NODES; i++) g_num_patterns *= 5;

    int *patterns = (int *)malloc((size_t)g_num_patterns * NUM_NODES * sizeof(int));
    gen_input_patterns(patterns);

    counter_example_t *counter_examples = (counter_example_t *)malloc((size_t)MAX_CEX * sizeof(counter_example_t));
    int num_cex = 1;

    /* Initial counter-example: all abort, no crash, loss all true */
    for (int i = 0; i < NUM_NODES; i++) counter_examples[0].init[i] = 0;
    for (int r = 0; r < NUM_ROUNDS; r++) {
        for (int i = 0; i < NUM_NODES; i++) {
            counter_examples[0].crash_send[r][i] = false;
            counter_examples[0].crash_after[r][i] = false;
        }
    }
    for (int r = 0; r < NUM_ROUNDS; r++) {
        for (int src = 0; src < NUM_NODES; src++) {
            for (int dst = 0; dst < NUM_NODES; dst++)
                counter_examples[0].loss[r][src][dst] = true;
        }
    }

    int iteration = 0;
    double tot_synth_gen = 0, tot_synth_solve = 0, tot_synth_model = 0, tot_synth_total = 0;
    double tot_synth_vars_mk = 0, tot_synth_vars_add = 0, tot_synth_trace = 0, tot_synth_agree = 0;
    double tot_verify_gen = 0, tot_verify_solve = 0, tot_verify_model = 0, tot_verify_total = 0;
    double tot_verify_env = 0, tot_verify_loss = 0, tot_verify_trace = 0, tot_verify_violation = 0;

    for (;;) {
        iteration++;
        if (iteration > MAX_ITER) {
            printf("Max iterations (%d) reached; no protocol found.\n", MAX_ITER);
            break;
        }
        Z3_config cfg = Z3_mk_config();
        Z3_set_param_value(cfg, "model", "true");
        Z3_context ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);

        printf("\n=== CEGIS Iteration %d (Atomic Commit) ===\n", iteration);

        protocol_t candidate;
        candidate.sm = (int *)malloc((size_t)NUM_ROUNDS * g_num_patterns * sizeof(int));
        timing_t t_synth;
        if (!synthesize(ctx, counter_examples, num_cex, patterns, &candidate, &t_synth)) {
            free(candidate.sm);
            Z3_del_context(ctx);
            printf("ERROR: Impossible to synthesize logic for these constraints.\n");
            printf("\n[total] %d iterations\n", iteration);
            printf("  Synthesize: vars_mk=%.3fs vars_add=%.3fs trace=%.3fs agree_validity=%.3fs gen=%.3fs solve=%.3fs model=%.3fs total=%.3fs\n",
                   tot_synth_vars_mk, tot_synth_vars_add, tot_synth_trace, tot_synth_agree, tot_synth_gen, tot_synth_solve, tot_synth_model, tot_synth_total);
            printf("  Verify:    env=%.3fs loss=%.3fs trace=%.3fs violation=%.3fs gen=%.3fs solve=%.3fs model=%.3fs total=%.3fs\n",
                   tot_verify_env, tot_verify_loss, tot_verify_trace, tot_verify_violation, tot_verify_gen, tot_verify_solve, tot_verify_model, tot_verify_total);
            printf("  Grand total: %.3fs\n", tot_synth_total + tot_verify_total);
            break;
        }
        tot_synth_gen += t_synth.gen;
        tot_synth_solve += t_synth.solve;
        tot_synth_model += t_synth.model;
        tot_synth_total += t_synth.total;
        tot_synth_vars_mk += t_synth.vars_mk;
        tot_synth_vars_add += t_synth.vars_add;
        tot_synth_trace += t_synth.trace;
        tot_synth_agree += t_synth.agree_validity;
        printf("  [time] Synthesize total: %.3fs\n", t_synth.total);
        printf("Candidate Generated.\n");

        counter_example_t cex;
        timing_t t_verify;
        int vret = verify(ctx, &candidate, patterns, &cex, &t_verify);
        if (vret == 2) {
            Z3_del_context(ctx);
            printf("\nSUCCESS! Valid Atomic Commit Protocol Synthesized.\n");
            printf("============================================================\n");
            printf("generated protocol (SM table): 0=Abort, 1=Commit, 2=DoNothing_Zero, 3=DoNothing_One\n");
            printf("============================================================\n");
            for (int r = 0; r < NUM_ROUNDS; r++) {
                printf("\nRound %d Rules:\n", r + 1);
                for (int p = 0; p < g_num_patterns && p < 10; p++) {
                    printf("  (");
                    for (int k = 0; k < NUM_NODES; k++) printf("%d%s", patterns[p * NUM_NODES + k], k < NUM_NODES - 1 ? "," : "");
                    printf(") -> %d\n", candidate.sm[r * g_num_patterns + p]);
                }
                if (g_num_patterns > 10) printf("  ... (%d patterns total)\n", g_num_patterns);
            }
            printf("\n============================================================\n");

            FILE *f = fopen("generated_protocol_atomic_commit.c", "w");
            if (f) {
                fprintf(f, "/* generated Atomic Commit protocol (CEGIS) */\n");
                fprintf(f, "#define NUM_NODES %d\n#define NUM_ROUNDS %d\n", NUM_NODES, NUM_ROUNDS);
                fprintf(f, "int PROTOCOL[%d][%d] = {\n", NUM_ROUNDS, g_num_patterns);
                for (int r = 0; r < NUM_ROUNDS; r++) {
                    fprintf(f, "  {");
                    for (int p = 0; p < g_num_patterns; p++) {
                        fprintf(f, "%d%s", candidate.sm[r * g_num_patterns + p], p < g_num_patterns - 1 ? "," : "");
                    }
                    fprintf(f, "}%s\n", r < NUM_ROUNDS - 1 ? "," : "");
                }
                fprintf(f, "};\n");
                fclose(f);
                printf("protocol saved to generated_protocol_atomic_commit.c\n");
            }

            free(candidate.sm);
            printf("\n[total] %d iterations\n", iteration);
            printf("  Synthesize: vars_mk=%.3fs vars_add=%.3fs trace=%.3fs agree_validity=%.3fs gen=%.3fs solve=%.3fs model=%.3fs total=%.3fs\n",
                   tot_synth_vars_mk, tot_synth_vars_add, tot_synth_trace, tot_synth_agree, tot_synth_gen, tot_synth_solve, tot_synth_model, tot_synth_total);
            printf("  Verify:    env=%.3fs loss=%.3fs trace=%.3fs violation=%.3fs gen=%.3fs solve=%.3fs model=%.3fs total=%.3fs\n",
                   tot_verify_env, tot_verify_loss, tot_verify_trace, tot_verify_violation, tot_verify_gen, tot_verify_solve, tot_verify_model, tot_verify_total);
            printf("  Grand total: %.3fs\n", tot_synth_total + tot_verify_total);
            break;
        }
        if (vret == 0) {
            free(candidate.sm);
            Z3_del_context(ctx);
            printf("Solver returned unknown (e.g. interrupted by Ctrl+C). Exiting without saving.\n");
            break;
        }

        tot_verify_gen += t_verify.gen;
        tot_verify_solve += t_verify.solve;
        tot_verify_model += t_verify.model;
        tot_verify_total += t_verify.total;
        tot_verify_env += t_verify.env;
        tot_verify_loss += t_verify.loss;
        tot_verify_trace += t_verify.trace;
        tot_verify_violation += t_verify.violation;
        printf("  [time] Verify total: %.3fs\n", t_verify.total);
        printf("FAILED. Counter-example found. Adding to set.\n");

        if (num_cex >= MAX_CEX) {
            free(candidate.sm);
            Z3_del_context(ctx);
            printf("ERROR: Too many counter-examples (%d). Increase MAX_CEX.\n", num_cex);
            break;
        }
        int is_dup = 0;
        for (int i = 0; i < num_cex; i++) {
            if (counter_example_equal(&cex, &counter_examples[i])) {
                is_dup = 1;
                break;
            }
        }
        if (is_dup) {
            free(candidate.sm);
            Z3_del_context(ctx);
            printf("Duplicate counterexample. Exiting.\n");
            break;
        }
        Z3_del_context(ctx);
        counter_examples[num_cex++] = cex;
        free(candidate.sm);
    }

    free(patterns);
    free(counter_examples);
    return 0;
}
