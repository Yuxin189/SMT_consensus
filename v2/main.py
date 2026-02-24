"""
========== Part 5: CEGIS main loop and I/O ==========
Initial counterexample, loop, output and save on success. To change save format or initial cex, edit the corresponding block in this file.
"""
import time
from synthesizer import Synthesizer
from verifier import Verifier
from config import NUM_NODES, INPUT_PATTERNS, NUM_ROUNDS


def main():
    syn = Synthesizer()
    ver = Verifier()

    # ---------- 5.1 Initial counterexample (change this to change the problem) ----------
    init_ce = [0] * NUM_NODES
    crash_send_ce = [[False] * NUM_NODES for _ in range(NUM_ROUNDS)]
    crash_after_ce = [[False] * NUM_NODES for _ in range(NUM_ROUNDS)]
    loss_ce = [[[True] * NUM_NODES for _ in range(NUM_NODES)] for _ in range(NUM_ROUNDS)]
    counter_examples = [(init_ce, crash_send_ce, crash_after_ce, loss_ce)]

    iteration = 0
    tot_synth = {"gen": 0.0, "solve": 0.0, "model": 0.0, "total": 0.0,
                 "vars_mk": 0.0, "vars_add": 0.0, "trace": 0.0, "agree_validity": 0.0}
    tot_verify = {"gen": 0.0, "solve": 0.0, "model": 0.0, "total": 0.0,
                  "env": 0.0, "loss": 0.0, "trace": 0.0, "violation": 0.0}

    # ---------- 5.2 CEGIS loop: synthesize -> verify -> if cex found add it and repeat ----------
    while True:
        iteration += 1
        print(f"\n=== CEGIS Iteration {iteration} ===")

        candidate_sm, t_synth = syn.synthesize(counter_examples)
        for k in t_synth:
            if k in tot_synth:
                tot_synth[k] += t_synth[k]
        print(f"  [time] Synthesize total: {t_synth['total']:.2f}s")

        if candidate_sm is None:
            print("ERROR: Impossible to synthesize logic for these constraints.")
            print(f"\n[total] {iteration} iterations")
            print(f"  Synthesize: vars_mk={tot_synth['vars_mk']:.2f}s vars_add={tot_synth['vars_add']:.2f}s trace={tot_synth['trace']:.2f}s agree_validity={tot_synth['agree_validity']:.2f}s gen={tot_synth['gen']:.2f}s solve={tot_synth['solve']:.2f}s model={tot_synth['model']:.2f}s total={tot_synth['total']:.2f}s")
            print(f"  Verify:    env={tot_verify['env']:.2f}s loss={tot_verify['loss']:.2f}s trace={tot_verify['trace']:.2f}s violation={tot_verify['violation']:.2f}s gen={tot_verify['gen']:.2f}s solve={tot_verify['solve']:.2f}s model={tot_verify['model']:.2f}s total={tot_verify['total']:.2f}s")
            print(f"  Grand total: {tot_synth['total'] + tot_verify['total']:.2f}s")
            break

        print("Candidate Generated.")

        result, t_verify = ver.verify(candidate_sm)
        for k in t_verify:
            if k in tot_verify:
                tot_verify[k] += t_verify[k]
        print(f"  [time] Verify total: {t_verify['total']:.2f}s")

        if result is None:
            # ---------- 5.3 Success: print and save protocol (change output format or filename here) ----------
            print("\nSUCCESS! Valid Distributed Protocol Synthesized.")
            print("=" * 60)
            print("generated protocol (SM table): input pattern (node0, node1, ...) -> output 0/1")
            print("0/1=received, 2=missing")
            print("=" * 60)
            for r, logic in enumerate(candidate_sm):
                print(f"\nRound {r+1} Rules:")
                for p, pattern in enumerate(INPUT_PATTERNS):
                    print(f"  {pattern} -> {logic[p]}")
            print("\n" + "=" * 60)

            with open("generated_protocol_v2.py", "w") as f:
                f.write("# generated consensus protocol (CEGIS v2)\n")
                f.write("# format: SM[round][pattern_idx] = 0 or 1\n")
                f.write("# INPUT_PATTERNS: values in {0,1,2} where 2=missing\n\n")
                f.write("PROTOCOL = " + repr(candidate_sm) + "\n")
                f.write("\nINPUT_PATTERNS = " + repr(list(INPUT_PATTERNS)) + "\n")
            print("protocol saved to generated_protocol_v2.py")
            print(f"\n[total] {iteration} iterations")
            print(f"  Synthesize: vars_mk={tot_synth['vars_mk']:.2f}s vars_add={tot_synth['vars_add']:.2f}s trace={tot_synth['trace']:.2f}s agree_validity={tot_synth['agree_validity']:.2f}s gen={tot_synth['gen']:.2f}s solve={tot_synth['solve']:.2f}s model={tot_synth['model']:.2f}s total={tot_synth['total']:.2f}s")
            print(f"  Verify:    env={tot_verify['env']:.2f}s loss={tot_verify['loss']:.2f}s trace={tot_verify['trace']:.2f}s violation={tot_verify['violation']:.2f}s gen={tot_verify['gen']:.2f}s solve={tot_verify['solve']:.2f}s model={tot_verify['model']:.2f}s total={tot_verify['total']:.2f}s")
            print(f"  Grand total: {tot_synth['total'] + tot_verify['total']:.2f}s")
            break
        else:
            print("FAILED. Counter-example found (Crash scenario). Adding to set.")
            counter_examples.append(result)


if __name__ == "__main__":
    main()