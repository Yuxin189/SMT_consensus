"""
========== Part 3: Synthesizer ==========
Find a candidate SM table from current counterexamples. To change correctness (e.g. different consensus conditions), edit block 3.2 only.
"""
import time
from z3 import *
from config import NUM_NODES, NUM_ROUNDS, INPUT_PATTERNS
from system_model import build_execution_trace


def compute_alive_from_crash_after(c_crash_after):
    """alive[r][i] = alive at start of round r+1 (r=0..NUM_ROUNDS)"""
    alive = [[True] * NUM_NODES]  # r=0: start of round 1
    for r in range(NUM_ROUNDS):
        row = [alive[r][i] and not c_crash_after[r][i] for i in range(NUM_NODES)]
        alive.append(row)
    return alive


class Synthesizer:
    def synthesize(self, counter_examples):
        print(f"[Synthesizer] Solving for {len(counter_examples)} ...")
        s = Solver()
        t_start = time.perf_counter()

        # ---------- 3.1 Protocol variables: one 0/1 per round per pattern (SM table) ----------
        t0 = time.perf_counter()
        sm_vars = []
        for r in range(NUM_ROUNDS):
            round_vars = []
            for p in range(len(INPUT_PATTERNS)):
                v = Int(f"SM_R{r+1}_P{p}")
                round_vars.append(v)
            sm_vars.append(round_vars)
        t_vars_mk = time.perf_counter() - t0
        t0 = time.perf_counter()
        for r in range(NUM_ROUNDS):
            for p in range(len(INPUT_PATTERNS)):
                s.add(Or(sm_vars[r][p] == 0, sm_vars[r][p] == 1))
        t_vars_add = time.perf_counter() - t0
        t_vars = t_vars_mk + t_vars_add

        # ---------- 3.2 Per counterexample: execution trace + correctness constraints ----------
        t_trace = 0.0
        t_agree = 0.0
        for idx, (c_init, c_crash_send, c_crash_after, c_loss) in enumerate(counter_examples):
            alive_ce = compute_alive_from_crash_after(c_crash_after)
            t0 = time.perf_counter()
            S = build_execution_trace(s, sm_vars, c_init, alive_ce, c_loss, trace_name_suffix=f"ce{idx}")
            t_trace += time.perf_counter() - t0

            # Deciders: alive at start of last round
            deciders = [alive_ce[NUM_ROUNDS - 1][i] for i in range(NUM_NODES)]

            # ----- Correctness: Agreement (survivors agree) + Validity (all-0 -> 0, all-1 -> 1) -----
            t0 = time.perf_counter()
            for i in range(NUM_NODES):
                for j in range(i + 1, NUM_NODES):
                    s.add(Implies(And(deciders[i], deciders[j]), S[NUM_ROUNDS][i] == S[NUM_ROUNDS][j]))

            if all(v == 0 for v in c_init):
                for i in range(NUM_NODES):
                    s.add(Implies(deciders[i], S[NUM_ROUNDS][i] == 0))
            if all(v == 1 for v in c_init):
                for i in range(NUM_NODES):
                    s.add(Implies(deciders[i], S[NUM_ROUNDS][i] == 1))
            t_agree += time.perf_counter() - t0
        t_cex = t_trace + t_agree

        t0 = time.perf_counter()
        if s.check() == sat:
            t_solve = time.perf_counter() - t0
            t0 = time.perf_counter()
            m = s.model()
            concrete_sm = []
            for r in range(NUM_ROUNDS):
                row = [m[sm_vars[r][p]].as_long() for p in range(len(INPUT_PATTERNS))]
                concrete_sm.append(row)
            t_model = time.perf_counter() - t0
            t_total = time.perf_counter() - t_start
            t_gen = t_vars + t_cex
            timing = {"gen": t_gen, "solve": t_solve, "model": t_model, "total": t_total,
                      "vars_mk": t_vars_mk, "vars_add": t_vars_add, "trace": t_trace, "agree_validity": t_agree}
            print(f"[Synthesizer][time] gen: vars_mk={t_vars_mk:.3f}s vars_add={t_vars_add:.3f}s trace={t_trace:.3f}s agree_validity={t_agree:.3f}s total_gen={t_gen:.2f}s | solve={t_solve:.2f}s model={t_model:.2f}s total={t_total:.2f}s")
            return concrete_sm, timing
        else:
            t_solve = time.perf_counter() - t0
            t_total = time.perf_counter() - t_start
            t_gen = t_vars + t_cex
            timing = {"gen": t_gen, "solve": t_solve, "model": 0.0, "total": t_total,
                      "vars_mk": t_vars_mk, "vars_add": t_vars_add, "trace": t_trace, "agree_validity": t_agree}
            print(f"[Synthesizer][time] gen: vars_mk={t_vars_mk:.3f}s vars_add={t_vars_add:.3f}s trace={t_trace:.3f}s agree_validity={t_agree:.3f}s total_gen={t_gen:.2f}s | solve={t_solve:.2f}s total={t_total:.2f}s")
            return None, timing
