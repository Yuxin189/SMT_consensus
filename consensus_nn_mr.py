# in general n nodes m rounds
from z3 import *

def check_nnmr_receive0(N: int, R: int):
    s = Solver()
    nodes = list(range(1, N + 1))   # 1...N
    T = list(range(R + 1))          # 0...R
    ROUNDS = list(range(1, R + 1))  # 1...R

    # init[i]: True means initial value is 1, False means initial value is 0
    init = {i: Bool(f"init_{i}") for i in nodes}

    # C[i][t]: True means node i has crashed by end of round t (will not return)
    C = {i: {t: Bool(f"C_{i}_{t}") for t in T} for i in nodes}

    # M[(sender,receiver,t)]: True means message sender->receiver in round t is delivered
    M = {(sender, receiver, t): Bool(f"M_{sender}_{receiver}_{t}")
         for sender in nodes for receiver in nodes if sender != receiver
         for t in ROUNDS}

    # S[i][t]: True means node i has received 0 by end of round t
    S = {i: {t: Bool(f"S_{i}_{t}") for t in T} for i in nodes}

    # Every nodes survives initially
    for i in nodes:
        s.add(C[i][0] == False)

    # Nodes can crash at any round and will not return if they do so: C(t) -> C(t+1)
    for i in nodes:
        for t in range(R):
            s.add(Implies(C[i][t], C[i][t + 1]))

    # We can assume there is always a surviving (non-crashed) node at the end
    s.add(Or([Not(C[i][R]) for i in nodes]))

    # If a node crashes, only some of its messages can be assumed lost, i.e., its message may be received by some nodes but not others.
    # If both sender and receiver survive at the end of round r, delivery must happen in round r
    for sender in nodes:
        for receiver in nodes:
            if sender == receiver:
                continue
            for t in ROUNDS:
                # Reliability: If both alive at end of round, message MUST be delivered
                s.add(Implies(And(Not(C[sender][t]), Not(C[receiver][t])), M[(sender, receiver, t)]))
                # If delivered, sender must be alive at start of round
                s.add(Implies(M[(sender, receiver, t)], Not(C[sender][t - 1])))
                # If delivered, receiver must be alive at end of round
                s.add(Implies(M[(sender, receiver, t)], Not(C[receiver][t])))


### Protocol: if receive 0 then become 0
    for i in nodes:
        s.add(S[i][0] == Not(init[i]))

    # Update each round:
    # S_i(t) = S_i(t-1) OR (exists j != i: M_{j->i}(t) AND S_j(t-1))
    for i in nodes:
        for t in ROUNDS:
            incoming = [And(M[(j, i, t)], S[j][t - 1]) for j in nodes if j != i]
            s.add(S[i][t] == Or(S[i][t - 1], Or(incoming)))

    # Decision: decide 0 iff receive0; else decide 1 (True means decide 1, False means decide 0)
    Decide1 = {i: Bool(f"Decide1_{i}") for i in nodes}
    for i in nodes:
        s.add(Decide1[i] == Not(S[i][R]))

    # CHECK 1: VALIDITY (All initial 0 -> Must decide 0)
    print("--- 1. Checking Validity (All-0 Input) ---")
    s.push()
    s.add(And([Not(init[i]) for i in nodes]))

    violation_all_0 = Or([And(Not(C[i][R]), Decide1[i]) for i in nodes])
    s.add(violation_all_0)
    
    if s.check() == sat:
        print(f"[FAIL] Validity (All-0) FAILED! Found counterexample.")
    else:
        print(f"[PASS] Validity (All-0) PASSED.")
    
    s.pop() # Restore clean state

    # CHECK 2: VALIDITY (All initial 1 -> Must decide 1)
    print("--- 2. Checking Validity (All-1 Input) ---")
    s.push()
    s.add(And([init[i] for i in nodes]))

    violation_all_1 = Or([And(Not(C[i][R]), Not(Decide1[i])) for i in nodes])
    s.add(violation_all_1)
    
    if s.check() == sat:
        print(f"[FAIL] Validity (All-1) FAILED! Found counterexample.")
    else:
        print(f"[PASS] Validity (All-1) PASSED.")
        
    s.pop() # Restore clean state

    # CHECK 3: AGREEMENT (All survivors must agree)
    print("--- 3. Checking Agreement ---")
    s.push() # Save clean state
    
    # Violation: Exists two survivors i, j such that Decide1[i] != Decide1[j]
    disagreements = []
    for i in nodes:
        for j in nodes:
            if i < j:
                disagreements.append(And(Not(C[i][R]), Not(C[j][R]), Decide1[i] != Decide1[j]))
    s.add(Or(disagreements))

    res = s.check()
    if res == sat:
        print(f"[FAIL] Agreement Check FAILED! Found counterexample:")
        m = s.model()
        # Print details of the counterexample
        print("\n--- Counterexample Details ---")
        for i in nodes:
            print(f" init[{i}] (True=1):", m.evaluate(init[i], model_completion=True),
                  f" crashed_end (C[{i}][{R}]):", m.evaluate(C[i][R], model_completion=True),
                  f" Decide1[{i}]:", m.evaluate(Decide1[i], model_completion=True))
            
    else:
        print(f"[PASS] Agreement Check PASSED. (Safe)")

    s.pop()

if __name__ == "__main__":
    check_nnmr_receive0(N=10, R=8)
