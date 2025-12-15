# three nodes: A, B, C ; three rounds: 1, 2, 3
from z3 import *

def check_3n3r_receive0():
    s = Solver()

    # Nodes: A=0, B=1, C=2
    A, B, C = 0, 1, 2
    # T: 0 means init, 1 means round1 ends, 2 means round2 ends, 3 means round3 ends
    T = [0, 1, 2, 3]
    # ROUNDS: sending message
    ROUNDS = [1, 2, 3]

    # initX: True means initial value is 1, False means initial value is 0
    initA, initB, initC = Bools("initA initB initC")

    # C_X_t : True means node X has crashed by end of round t (will not return)
    C_A = [Bool(f"C_A_{t}") for t in T]
    C_B = [Bool(f"C_B_{t}") for t in T]
    C_C = [Bool(f"C_C_{t}") for t in T]

    # M_XY_t : True means message from node X to node Y in round t is delivered
    M_AB = {t: Bool(f"M_AB_{t}") for t in ROUNDS}
    M_AC = {t: Bool(f"M_AC_{t}") for t in ROUNDS}
    M_BA = {t: Bool(f"M_BA_{t}") for t in ROUNDS}
    M_BC = {t: Bool(f"M_BC_{t}") for t in ROUNDS}
    M_CA = {t: Bool(f"M_CA_{t}") for t in ROUNDS}
    M_CB = {t: Bool(f"M_CB_{t}") for t in ROUNDS}

    # S_X_t : True means node X has received 0 by end of round t
    S_A = [Bool(f"S_A_{t}") for t in T]
    S_B = [Bool(f"S_B_{t}") for t in T]
    S_C = [Bool(f"S_C_{t}") for t in T]

    # Every nodes survive initially
    s.add(C_A[0] == False)
    s.add(C_B[0] == False)
    s.add(C_C[0] == False)

    # Nodes can crash at any round and will not return if they do so: C(t) -> C(t+1)
    s.add(Implies(C_A[0], C_A[1]))
    s.add(Implies(C_A[1], C_A[2]))
    s.add(Implies(C_A[2], C_A[3]))

    s.add(Implies(C_B[0], C_B[1]))
    s.add(Implies(C_B[1], C_B[2]))
    s.add(Implies(C_B[2], C_B[3]))

    s.add(Implies(C_C[0], C_C[1]))
    s.add(Implies(C_C[1], C_C[2]))
    s.add(Implies(C_C[2], C_C[3]))

    # We can assume there is always a surviving (non-crashed) node at the end
    s.add(Or(Not(C_A[3]), Not(C_B[3]), Not(C_C[3])))

    # If a node crashes, only some of its messages can be assumed lost, i.e., its message may be received by some nodes but not others.
    # If both sender and receiver survive at the end of round r, delivery must happen in round r
    for t in ROUNDS:
        # Both alive -> Delivered
        # Delivered -> Sender alive at start
        # Delivered -> Receiver alive at end
        # Link A <-> B
        s.add(Implies(And(Not(C_A[t]), Not(C_B[t])), M_AB[t]))
        s.add(Implies(M_AB[t], Not(C_A[t-1])))
        s.add(Implies(M_AB[t], Not(C_B[t])))

        s.add(Implies(And(Not(C_B[t]), Not(C_A[t])), M_BA[t]))
        s.add(Implies(M_BA[t], Not(C_B[t-1])))
        s.add(Implies(M_BA[t], Not(C_A[t])))

        # Link A <-> C
        s.add(Implies(And(Not(C_A[t]), Not(C_C[t])), M_AC[t]))
        s.add(Implies(M_AC[t], Not(C_A[t-1])))
        s.add(Implies(M_AC[t], Not(C_C[t])))

        s.add(Implies(And(Not(C_C[t]), Not(C_A[t])), M_CA[t]))
        s.add(Implies(M_CA[t], Not(C_C[t-1])))
        s.add(Implies(M_CA[t], Not(C_A[t])))

        # Link B <-> C
        s.add(Implies(And(Not(C_B[t]), Not(C_C[t])), M_BC[t]))
        s.add(Implies(M_BC[t], Not(C_B[t-1])))
        s.add(Implies(M_BC[t], Not(C_C[t])))

        s.add(Implies(And(Not(C_C[t]), Not(C_B[t])), M_CB[t]))
        s.add(Implies(M_CB[t], Not(C_C[t-1])))
        s.add(Implies(M_CB[t], Not(C_B[t])))

### Protocol: if receive 0 then become 0
    s.add(S_A[0] == Not(initA))
    s.add(S_B[0] == Not(initB))
    s.add(S_C[0] == Not(initC))

    # Round 1:
    s.add(S_A[1] == Or(S_A[0], And(M_BA[1], S_B[0]), And(M_CA[1], S_C[0])))
    s.add(S_B[1] == Or(S_B[0], And(M_AB[1], S_A[0]), And(M_CB[1], S_C[0])))
    s.add(S_C[1] == Or(S_C[0], And(M_AC[1], S_A[0]), And(M_BC[1], S_B[0])))

    # Round 2:
    s.add(S_A[2] == Or(S_A[1], And(M_BA[2], S_B[1]), And(M_CA[2], S_C[1])))
    s.add(S_B[2] == Or(S_B[1], And(M_AB[2], S_A[1]), And(M_CB[2], S_C[1])))
    s.add(S_C[2] == Or(S_C[1], And(M_AC[2], S_A[1]), And(M_BC[2], S_B[1])))

    # Round 3:
    s.add(S_A[3] == Or(S_A[2], And(M_BA[3], S_B[2]), And(M_CA[3], S_C[2])))
    s.add(S_B[3] == Or(S_B[2], And(M_AB[3], S_A[2]), And(M_CB[3], S_C[2])))
    s.add(S_C[3] == Or(S_C[2], And(M_AC[3], S_A[2]), And(M_BC[3], S_B[2])))

    # Decision: decide 0 iff receive0; else decide 1  (True means decide 1, False means decide 0)
    Decide1_A = Bool("Decide1_A")
    Decide1_B = Bool("Decide1_B")
    Decide1_C = Bool("Decide1_C")
    s.add(Decide1_A == Not(S_A[3]))
    s.add(Decide1_B == Not(S_B[3]))
    s.add(Decide1_C == Not(S_C[3]))

    # CHECK 1: VALIDITY (All inputs 0 -> Must decide 0)
    print("\n--- 1. Checking Validity (All-0 Input) ---")
    s.push()
    s.add(And(Not(initA), Not(initB), Not(initC)))
    
    # Violation: At least one survivor decides 1
    violation_all_0 = Or(
        And(Not(C_A[3]), Decide1_A),
        And(Not(C_B[3]), Decide1_B),
        And(Not(C_C[3]), Decide1_C)
    )
    s.add(violation_all_0)
    
    if s.check() == sat:
        print("Validity Check (All-0) FAILED! Found counterexample.")
        print(s.model())
    else:
        print("Validity Check (All-0) PASSED.")
    
    s.pop()

    # CHECK 2: VALIDITY (All inputs 1 -> Must decide 1)
    print("\n--- 2. Checking Validity (All-1 Input) ---")
    s.push() # Save state
    s.add(And(initA, initB, initC))
    
    # Violation: At least one survivor decides 0 (Decide1 is False)
    violation_all_1 = Or(
        And(Not(C_A[3]), Not(Decide1_A)),
        And(Not(C_B[3]), Not(Decide1_B)),
        And(Not(C_C[3]), Not(Decide1_C))
    )
    s.add(violation_all_1)
    
    if s.check() == sat:
        print("Validity Check (All-1) FAILED! Found counterexample.")
        print(s.model())
    else:
        print("Validity Check (All-1) PASSED.")
        
    s.pop()

    # CHECK 3: AGREEMENT (Survivors must agree)
    print("\n--- 3. Checking Agreement ---")
    s.push() 

    disj = []
    disj.append(And(Not(C_A[3]), Not(C_B[3]), Decide1_A != Decide1_B))
    disj.append(And(Not(C_A[3]), Not(C_C[3]), Decide1_A != Decide1_C))
    disj.append(And(Not(C_B[3]), Not(C_C[3]), Decide1_B != Decide1_C))
    s.add(Or(disj))

    if s.check() == sat:
        print("Agreement Check FAILED! Found counterexample:")
        m = s.model()
        print(" initA:", m.evaluate(initA), " initB:", m.evaluate(initB), " initC:", m.evaluate(initC))
        print(" Decide1_A:", m.evaluate(Decide1_A), " Decide1_B:", m.evaluate(Decide1_B), " Decide1_C:", m.evaluate(Decide1_C))
    else:
        print("Agreement Check PASSED.")
    
    s.pop()

if __name__ == "__main__":
    check_3n3r_receive0()
