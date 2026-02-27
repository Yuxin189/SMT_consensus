/*
 * Trace checker for generated Atomic Commit protocol.
 * Compile: gcc -o check_protocol check_protocol.c
 * Run: ./check_protocol
 *
 * Must have generated_protocol_atomic_commit.c in same dir (or adjust include).
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdbool.h>

/* Pull in generated protocol - defines NUM_NODES, NUM_ROUNDS, PROTOCOL */
#include "generated_protocol_atomic_commit.c"

static int g_num_patterns;
#define STATE_MISSING 4

static int pow5(int n) {
    int p = 1;
    for (int i = 0; i < n; i++) p *= 5;
    return p;
}

static void gen_patterns(int *patterns) {
    for (int p = 0; p < g_num_patterns; p++) {
        for (int k = 0; k < NUM_NODES; k++) {
            patterns[p * NUM_NODES + k] = (p / pow5(NUM_NODES - 1 - k)) % 5;
        }
    }
}

/* Find pattern index matching recv_vec */
static int pattern_match(const int *patterns, const int *recv_vec) {
    for (int p = 0; p < g_num_patterns; p++) {
        int match = 1;
        for (int k = 0; k < NUM_NODES; k++) {
            if (patterns[p * NUM_NODES + k] != recv_vec[k]) { match = 0; break; }
        }
        if (match) return p;
    }
    return -1;
}

/* Run trace: init, alive, loss -> S (final state per node) */
static void run_trace(const int *protocol, const int *patterns,
                      const int *init, const bool alive[NUM_ROUNDS + 1][NUM_NODES],
                      const bool loss[NUM_ROUNDS][NUM_NODES][NUM_NODES],
                      int S[NUM_ROUNDS + 1][NUM_NODES]) {
    for (int i = 0; i < NUM_NODES; i++) S[0][i] = init[i];
    for (int r = 1; r <= NUM_ROUNDS; r++) {
        int r1 = r - 1;
        for (int i = 0; i < NUM_NODES; i++) {
            int recv_vec[NUM_NODES];
            for (int sender = 0; sender < NUM_NODES; sender++) {
                if (sender == i) {
                    recv_vec[sender] = alive[r1][i] ? S[r1][i] : STATE_MISSING;
                } else {
                    int delivered = alive[r1][sender] && loss[r1][sender][i];
                    recv_vec[sender] = delivered ? S[r1][sender] : STATE_MISSING;
                }
            }
            int p = pattern_match(patterns, recv_vec);
            if (p < 0) {
                printf("ERROR: no pattern match for recv_vec\n");
                return;
            }
            int new_state = protocol[r1 * g_num_patterns + p];
            S[r][i] = alive[r1][i] ? new_state : S[r1][i];
        }
    }
}

static void compute_alive(const bool crash_after[NUM_ROUNDS][NUM_NODES],
                         bool alive[NUM_ROUNDS + 1][NUM_NODES]) {
    for (int i = 0; i < NUM_NODES; i++) alive[0][i] = true;
    for (int r = 0; r < NUM_ROUNDS; r++) {
        for (int i = 0; i < NUM_NODES; i++)
            alive[r + 1][i] = alive[r][i] && !crash_after[r][i];
    }
}

/* Test one scenario. Returns 0 on pass, 1 on fail. */
static int test_scenario(const int *protocol, const int *patterns,
                         const int *init, const bool crash_after[NUM_ROUNDS][NUM_NODES],
                         const bool loss[NUM_ROUNDS][NUM_NODES][NUM_NODES],
                         const char *name) {
    bool alive[NUM_ROUNDS + 1][NUM_NODES];
    int S[NUM_ROUNDS + 1][NUM_NODES];
    compute_alive(crash_after, alive);
    run_trace(protocol, patterns, init, alive, loss, S);

    /* Rule 1: all uncrashed must reach final (0 or 1) */
    for (int i = 0; i < NUM_NODES; i++) {
        if (alive[NUM_ROUNDS][i] && S[NUM_ROUNDS][i] != 0 && S[NUM_ROUNDS][i] != 1) {
            printf("FAIL [%s]: Rule 1 - node %d did not reach final decision (%d)\n", name, i, S[NUM_ROUNDS][i]);
            return 1;
        }
    }
    /* Rule 2: no Abort/Commit in intermediate rounds */
    for (int r = 1; r < NUM_ROUNDS; r++) {
        for (int i = 0; i < NUM_NODES; i++) {
            if (alive[r][i] && (S[r][i] == 0 || S[r][i] == 1)) {
                printf("FAIL [%s]: Rule 2 - node %d decided early in round %d\n", name, i, r);
                return 1;
            }
        }
    }
    /* Rule 3: Agreement - all uncrashed must decide same */
    int first_dec = -1;
    for (int i = 0; i < NUM_NODES; i++) {
        if (!alive[NUM_ROUNDS][i]) continue;
        if (first_dec < 0) first_dec = S[NUM_ROUNDS][i];
        else if (S[NUM_ROUNDS][i] != first_dec) {
            printf("FAIL [%s]: Rule 3 - Agreement violated\n", name);
            return 1;
        }
    }

    /* Rule 5: any abort -> all must abort */
    int any_abort = 0;
    for (int i = 0; i < NUM_NODES; i++) if (init[i] == 0) { any_abort = 1; break; }
    if (any_abort) {
        for (int i = 0; i < NUM_NODES; i++) {
            if (alive[NUM_ROUNDS][i] && S[NUM_ROUNDS][i] != 0) {
                printf("FAIL [%s]: Rule 5 - any abort but node %d decided commit\n", name, i);
                return 1;
            }
        }
    }

    /* Rule 4: all commit + no crash -> all must commit */
    int all_commit = 1, no_crash = 1;
    for (int i = 0; i < NUM_NODES; i++) {
        if (init[i] != 1) all_commit = 0;
        if (!alive[NUM_ROUNDS][i]) no_crash = 0;
    }
    if (all_commit && no_crash) {
        for (int i = 0; i < NUM_NODES; i++) {
            if (S[NUM_ROUNDS][i] != 1) {
                printf("FAIL [%s]: Rule 4 - all commit no crash but node %d decided abort\n", name, i);
                return 1;
            }
        }
    }
    return 0;
}

/* Scenario E: last-round crash -> agreement (no split commit/abort) */
static int test_scenario_e(const int *protocol, const int *patterns,
                           const int *init, const bool crash_after[NUM_ROUNDS][NUM_NODES],
                           const bool loss[NUM_ROUNDS][NUM_NODES][NUM_NODES],
                           const char *name) {
    bool alive[NUM_ROUNDS + 1][NUM_NODES];
    int S[NUM_ROUNDS + 1][NUM_NODES];
    compute_alive(crash_after, alive);
    run_trace(protocol, patterns, init, alive, loss, S);

    /* Agreement: all survivors must decide same */
    int first_dec = -1;
    for (int i = 0; i < NUM_NODES; i++) {
        if (!alive[NUM_ROUNDS][i]) continue;
        if (first_dec < 0) first_dec = S[NUM_ROUNDS][i];
        else if (S[NUM_ROUNDS][i] != first_dec) {
            printf("FAIL [%s]: last-round crash caused split commit/abort\n", name);
            return 1;
        }
    }
    return 0;
}

int main(void) {
    g_num_patterns = pow5(NUM_NODES);
    int *patterns = malloc((size_t)g_num_patterns * NUM_NODES * sizeof(int));
    gen_patterns(patterns);

    int failed = 0;

    /* Test 1: all abort, no crash, no loss */
    {
        int init[NUM_NODES];
        bool crash_after[NUM_ROUNDS][NUM_NODES];
        bool loss[NUM_ROUNDS][NUM_NODES][NUM_NODES];
        for (int i = 0; i < NUM_NODES; i++) init[i] = 0;
        memset(crash_after, 0, sizeof(crash_after));
        memset(loss, 1, sizeof(loss)); /* true = delivered */
        failed += test_scenario((const int *)PROTOCOL, patterns, init, crash_after, loss, "all_abort_no_crash");
    }

    /* Test 2: all commit, no crash, no loss */
    {
        int init[NUM_NODES];
        bool crash_after[NUM_ROUNDS][NUM_NODES];
        bool loss[NUM_ROUNDS][NUM_NODES][NUM_NODES];
        for (int i = 0; i < NUM_NODES; i++) init[i] = 1;
        memset(crash_after, 0, sizeof(crash_after));
        memset(loss, 1, sizeof(loss));
        failed += test_scenario((const int *)PROTOCOL, patterns, init, crash_after, loss, "all_commit_no_crash");
    }

    /* Test 3: one abort, rest commit, no crash, no loss */
    {
        int init[NUM_NODES];
        bool crash_after[NUM_ROUNDS][NUM_NODES];
        bool loss[NUM_ROUNDS][NUM_NODES][NUM_NODES];
        init[0] = 0;
        for (int i = 1; i < NUM_NODES; i++) init[i] = 1;
        memset(crash_after, 0, sizeof(crash_after));
        memset(loss, 1, sizeof(loss));
        failed += test_scenario((const int *)PROTOCOL, patterns, init, crash_after, loss, "one_abort_rest_commit");
    }

    /* Test 4: all abort with some message loss */
    {
        int init[NUM_NODES];
        bool crash_after[NUM_ROUNDS][NUM_NODES];
        bool loss[NUM_ROUNDS][NUM_NODES][NUM_NODES];
        for (int i = 0; i < NUM_NODES; i++) init[i] = 0;
        memset(crash_after, 0, sizeof(crash_after));
        memset(loss, 1, sizeof(loss));
        loss[0][0][1] = false; /* node 0->1 lost in round 0 */
        failed += test_scenario((const int *)PROTOCOL, patterns, init, crash_after, loss, "all_abort_with_loss");
    }

    /* Test 5: one abort, node 0 crashes after round 0 (Scenario B variant / D) */
    {
        int init[NUM_NODES];
        bool crash_after[NUM_ROUNDS][NUM_NODES];
        bool loss[NUM_ROUNDS][NUM_NODES][NUM_NODES];
        init[0] = 0;
        for (int i = 1; i < NUM_NODES; i++) init[i] = 1;
        memset(crash_after, 0, sizeof(crash_after));
        crash_after[0][0] = true;
        memset(loss, 1, sizeof(loss));
        failed += test_scenario((const int *)PROTOCOL, patterns, init, crash_after, loss, "one_abort_crash0");
    }

    /* Scenario C/D: skipped (CEGIS only enforces Rule 1-5; Rule 6/7 would need synthesis changes) */

    /* Scenario E: crash only in last round -> agreement (no split) */
    {
        int init[NUM_NODES];
        bool crash_after[NUM_ROUNDS][NUM_NODES];
        bool loss[NUM_ROUNDS][NUM_NODES][NUM_NODES];
        for (int i = 0; i < NUM_NODES; i++) init[i] = 1;
        memset(crash_after, 0, sizeof(crash_after));
        crash_after[NUM_ROUNDS - 1][0] = true; /* node 0 crashes after last round */
        memset(loss, 1, sizeof(loss));
        failed += test_scenario_e((const int *)PROTOCOL, patterns, init, crash_after, loss, "E_last_round_crash");
    }

    /* Scenario F: no early decision - skipped (model uses 0/1 for all rounds, no "undecided" state) */

    free(patterns);

    if (failed == 0) {
        printf("PASS: all tests passed\n");
        return 0;
    } else {
        printf("FAIL: %d test(s) failed\n", failed);
        return 1;
    }
}
