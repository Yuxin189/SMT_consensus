"""
========== Part 4: Verifier ==========
Use Z3 to check if there exists an environment (init/crash/loss) where the candidate protocol violates the spec.
To change which violations to check (e.g. different consensus conditions), edit block 4.4 only.
"""
import time
from z3 import *
from config import NUM_NODES, NUM_ROUNDS
from system_model import build_execution_trace


def is_true(val):
    """Whether value from model is True (m[BoolRef] is True/False; this normalizes to True check)."""
    return val == True


class Verifier:
    def verify(self, concrete_sm):
        print("[Verifier] Checking candidate SM...")
        t_total_start = time.perf_counter()
        t_env = 0.0
        t_loss = 0.0
        t_trace = 0.0
        t_violation = 0.0
        t_solve = 0.0
        s = Solver()

        # ---------- 4.1 Environment variables: init, alive, crash, loss ----------
        t0 = time.perf_counter()
        Init = [Int(f"Init_{i}") for i in range(NUM_NODES)]
        for i in range(NUM_NODES):
            s.add(Or(Init[i] == 0, Init[i] == 1))

        # Alive[r][i]: node i alive at start of round r+1 (r=0..NUM_ROUNDS)
        Alive = [[Bool(f"Alive_r{r}_n{i}") for i in range(NUM_NODES)] for r in range(NUM_ROUNDS + 1)]
        for i in range(NUM_NODES):
            s.add(Alive[0][i] == True)

        CrashSend = [[Bool(f"CrashSend_r{r}_n{i}") for i in range(NUM_NODES)] for r in range(NUM_ROUNDS)]
        CrashAfter = [[Bool(f"CrashAfter_r{r}_n{i}") for i in range(NUM_NODES)] for r in range(NUM_ROUNDS)]

        # ---------- 4.2 Alive evolution and Loss constraints (crash-stop + loss vs crash_send) ----------
        for r in range(NUM_ROUNDS):
            for i in range(NUM_NODES):
                s.add(Alive[r+1][i] == And(Alive[r][i], Not(CrashAfter[r][i])))
                s.add(Implies(Not(Alive[r][i]), And(Not(CrashSend[r][i]), Not(CrashAfter[r][i]))))
        for r in range(NUM_ROUNDS):
            for i in range(NUM_NODES):
                s.add(Implies(CrashSend[r][i], CrashAfter[r][i]))

        Loss = [[[Bool(f"Loss_r{r}_{src}_{dst}") for dst in range(NUM_NODES)]
                for src in range(NUM_NODES)] for r in range(NUM_ROUNDS)]
        t_env += time.perf_counter() - t0

        t0 = time.perf_counter()
        for r in range(NUM_ROUNDS):
            for src in range(NUM_NODES):
                for dst in range(NUM_NODES):
                    s.add(Implies(Not(Alive[r][src]), Loss[r][src][dst] == False))
                for dst in range(NUM_NODES):
                    s.add(Implies(And(Alive[r][src], Not(CrashSend[r][src])),
                                Loss[r][src][dst] == True))
                for dst in range(NUM_NODES):
                    s.add(Implies(And(Alive[r][src], Loss[r][src][dst] == False),
                                CrashSend[r][src] == True))
        for r in range(NUM_ROUNDS):
            for i in range(NUM_NODES):
                s.add(Implies(Alive[r][i], Loss[r][i][i] == True))
        t_loss += time.perf_counter() - t0

        # ---------- 4.3 Build execution trace with candidate SM ----------
        sm_logic_vals = [[IntVal(val) for val in row] for row in concrete_sm]
        t0 = time.perf_counter()
        S = build_execution_trace(s, sm_logic_vals, Init, Alive, Loss, trace_name_suffix="verify")
        t_trace += time.perf_counter() - t0

        # ---------- 4.4 Violation conditions: sat if any (Agreement / Validity / at least one survivor) ----------
        t0 = time.perf_counter()
        violation_conds = []

        # Agreement: two survivors decide differently
        for i in range(NUM_NODES):
            for j in range(i + 1, NUM_NODES):
                dec_i = Alive[NUM_ROUNDS - 1][i]
                dec_j = Alive[NUM_ROUNDS - 1][j]
                violation_conds.append(And(dec_i, dec_j, S[NUM_ROUNDS][i] != S[NUM_ROUNDS][j]))

        # Validity: all 0 but someone decides non-0; or all 1 but someone decides non-1
        all_zero = And([Init[i] == 0 for i in range(NUM_NODES)])
        all_one = And([Init[i] == 1 for i in range(NUM_NODES)])
        for i in range(NUM_NODES):
            dec_i = Alive[NUM_ROUNDS - 1][i]
            violation_conds.append(And(all_zero, dec_i, S[NUM_ROUNDS][i] != 0))
            violation_conds.append(And(all_one, dec_i, S[NUM_ROUNDS][i] != 1))

        s.add(Or(violation_conds))
        s.add(Or([Alive[NUM_ROUNDS][i] for i in range(NUM_NODES)]))  # at least one survivor at end
        t_violation += time.perf_counter() - t0

        t0 = time.perf_counter()
        result = s.check()
        t_solve += time.perf_counter() - t0
        t_gen = t_env + t_loss + t_trace + t_violation
        if result == sat:
            t0 = time.perf_counter()
            m = s.model()
            c_init = [m[Init[i]].as_long() for i in range(NUM_NODES)]
            c_crash_send = [[is_true(m[CrashSend[r][i]]) for i in range(NUM_NODES)] for r in range(NUM_ROUNDS)]
            c_crash_after = [[is_true(m[CrashAfter[r][i]]) for i in range(NUM_NODES)] for r in range(NUM_ROUNDS)]
            c_loss = [[[is_true(m[Loss[r][src][dst]]) for dst in range(NUM_NODES)]
                    for src in range(NUM_NODES)] for r in range(NUM_ROUNDS)]
            t_model = time.perf_counter() - t0
            t_total = time.perf_counter() - t_total_start
            timing = {"gen": t_gen, "solve": t_solve, "model": t_model, "total": t_total,
                      "env": t_env, "loss": t_loss, "trace": t_trace, "violation": t_violation}
            print(
                f"[Verifier][time] gen_constraints={t_gen:.2f}s, z3_solve={t_solve:.2f}s, model={t_model:.2f}s, total={t_total:.2f}s"
            )
            return (c_init, c_crash_send, c_crash_after, c_loss), timing
        else:
            t_total = time.perf_counter() - t_total_start
            timing = {"gen": t_gen, "solve": t_solve, "model": 0.0, "total": t_total,
                      "env": t_env, "loss": t_loss, "trace": t_trace, "violation": t_violation}
            print(
                f"[Verifier][time] gen_constraints={t_gen:.2f}s, z3_solve={t_solve:.2f}s, total={t_total:.2f}s"
            )
            return None, timing
