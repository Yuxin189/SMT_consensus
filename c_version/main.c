#include <stdio.h>
#include <stdlib.h>
#include <z3.h>

#include "config.h"
#include "common.h"
#include "synthesizer.h"
#include "verifier.h"

#define MAX_CEX  20000     /* max counterexamples array size */
#define MAX_ITER 8000      /* max CEGIS iterations */

int main(void) {
    /* NUM_PATTERNS = 3^NUM_NODES, works for any NUM_NODES */
    g_num_patterns = 1;
    for (int i = 0; i < NUM_NODES; i++) g_num_patterns *= 3;

    int *patterns = (int *)malloc((size_t)g_num_patterns * NUM_NODES * sizeof(int));
    gen_input_patterns(patterns);

    counter_example_t *counter_examples = (counter_example_t *)malloc((size_t)MAX_CEX * sizeof(counter_example_t));
    int num_cex = 1;

    /* Initial counter-example: same as v2 Python (all-zero init, no crash, loss all true = all delivered) */
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
    double tot_verify_gen = 0, tot_verify_solve = 0, tot_verify_model = 0, tot_verify_total = 0;

    for (;;) {
        iteration++;
        if (iteration > MAX_ITER) {
            printf("Max iterations (%d) reached; no protocol found. Try 4n4r in config.h.\n", MAX_ITER);
            break;
        }
        /* Fresh context per iteration (like Python), no AST accumulation, avoids Z3 overflow */
        Z3_config cfg = Z3_mk_config();
        Z3_set_param_value(cfg, "model", "true");
        Z3_context ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);

        printf("\n=== CEGIS Iteration %d ===\n", iteration);

        /* Same as Python: new context each round, use all counterexamples for synthesis */
        protocol_t candidate;
        candidate.sm = (int *)malloc((size_t)NUM_ROUNDS * g_num_patterns * sizeof(int));
        timing_t t_synth;
        if (!synthesize(ctx, counter_examples, num_cex, patterns, &candidate, &t_synth)) {
            free(candidate.sm);
            Z3_del_context(ctx);
            printf("ERROR: Impossible to synthesize logic for these constraints.\n");
            break;
        }
        tot_synth_gen += t_synth.gen;
        tot_synth_solve += t_synth.solve;
        tot_synth_model += t_synth.model;
        tot_synth_total += t_synth.total;
        printf("  [time] Synthesize total: %.3fs\n", t_synth.total);
        printf("Candidate Generated.\n");

        counter_example_t cex;
        timing_t t_verify;
        int vret = verify(ctx, &candidate, patterns, &cex, &t_verify);
        if (vret == 2) {
            Z3_del_context(ctx);
            printf("\nSUCCESS! Valid Distributed Protocol Synthesized.\n");
            printf("============================================================\n");
            printf("generated protocol (SM table): input pattern -> output 0/1\n");
            printf("0/1=received, 2=missing\n");
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

            FILE *f = fopen("generated_protocol_c.c", "w");
            if (f) {
                fprintf(f, "/* generated consensus protocol (CEGIS v2 port to C) */\n");
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
                printf("protocol saved to generated_protocol_c.c\n");
            }

            free(candidate.sm);
            printf("\n[total] %d iterations\n", iteration);
            printf("  Synthesize: gen=%.3fs solve=%.3fs model=%.3fs total=%.3fs\n",
                   tot_synth_gen, tot_synth_solve, tot_synth_model, tot_synth_total);
            printf("  Verify:    gen=%.3fs solve=%.3fs model=%.3fs total=%.3fs\n",
                   tot_verify_gen, tot_verify_solve, tot_verify_model, tot_verify_total);
            printf("  Grand total: %.3fs\n", tot_synth_total + tot_verify_total);
            break;  /* ctx already deleted above */
        }
        if (vret == 0) {
            free(candidate.sm);
            Z3_del_context(ctx);
            printf("Solver returned unknown (e.g. interrupted by Ctrl+C). Exiting without saving.\n");
            break;
        }

        /* vret == 1: counterexample found */
        tot_verify_gen += t_verify.gen;
        tot_verify_solve += t_verify.solve;
        tot_verify_model += t_verify.model;
        tot_verify_total += t_verify.total;
        printf("  [time] Verify total: %.3fs\n", t_verify.total);
        printf("FAILED. Counter-example found (Crash scenario). Adding to set.\n");

        if (num_cex >= MAX_CEX) {
            free(candidate.sm);
            Z3_del_context(ctx);
            printf("ERROR: Too many counter-examples (%d). Increase MAX_CEX in main.c, or try 4n4r in config.h (converges in ~137 iterations).\n", num_cex);
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
            printf("Duplicate counterexample (already in set). Exiting.\n");
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
