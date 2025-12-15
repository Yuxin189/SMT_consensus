# two nodes: A, B ; two rounds: 1, 2
from z3 import *

def check_2n2r_receive0():
    s = Solver()

    # Nodes: A=0, B=1
    A, B = 0, 1
    # T: 0 means init, 1 means round1 ends, 2 means round2 ends
    T = [0, 1, 2]
    # ROUNDS: sending message
    ROUNDS = [1, 2]

    # initX: True means initial value is 1, False means initial value is 0
    initA, initB = Bools("initA initB")

    # C_X_t : True means node X has crashed by end of round t (will not return)
    C_A = [Bool(f"C_A_{t}") for t in T]
    C_B = [Bool(f"C_B_{t}") for t in T]

    # M_XY_t : True means message from node X to node Y in round t is delivered
    M_AB = {t: Bool(f"M_AB_{t}") for t in ROUNDS}
    M_BA = {t: Bool(f"M_BA_{t}") for t in ROUNDS}

    # S_X_t : True means node X has received 0 by end of round t
    S_A = [Bool(f"S_A_{t}") for t in T]
    S_B = [Bool(f"S_B_{t}") for t in T]

    # Every nodes survive initially
    s.add(C_A[0] == False)
    s.add(C_B[0] == False)

    # Nodes can crash at any round and will not return if they do so: C(t) -> C(t+1)
    s.add(Implies(C_A[0], C_A[1]))
    s.add(Implies(C_A[1], C_A[2]))
    s.add(Implies(C_B[0], C_B[1]))
    s.add(Implies(C_B[1], C_B[2]))

    # We can assume there is always a surviving (non-crashed) node at the end
    s.add(Or(Not(C_A[2]), Not(C_B[2])))

    # If a node crashes, only some of its messages can be assumed lost, i.e., its message may be received by some nodes but not others.
    # If both sender and receiver survive at the end of round r, delivery must happen in round r
    for t in ROUNDS:
        s.add(Implies(And(Not(C_A[t]), Not(C_B[t])), M_AB[t]))
        s.add(Implies(And(Not(C_A[t]), Not(C_B[t])), M_BA[t]))


### Protocol: if receive 0 then become 0
    s.add(S_A[0] == Not(initA))
    s.add(S_B[0] == Not(initB))

    # Round 1:
    # S_A(1) = S_A(0) OR (M_BA(1) AND S_B(0))
    # S_B(1) = S_B(0) OR (M_AB(1) AND S_A(0))
    s.add(S_A[1] == Or(S_A[0], And(M_BA[1], S_B[0])))
    s.add(S_B[1] == Or(S_B[0], And(M_AB[1], S_A[0])))

    # Round 2:
    s.add(S_A[2] == Or(S_A[1], And(M_BA[2], S_B[1])))
    s.add(S_B[2] == Or(S_B[1], And(M_AB[2], S_A[1])))

    # Decision: decide 0 iff receive0; else decide 1
    # True means decide 1, False means decide 0
    Decide1_A = Bool("Decide1_A")
    Decide1_B = Bool("Decide1_B")
    s.add(Decide1_A == Not(S_A[2]))
    s.add(Decide1_B == Not(S_B[2]))

    # Check agreement by searching a counterexample
    # Both survive -> decisions differ
    s.add(Not(C_A[2]))          # A survives to the end
    s.add(Not(C_B[2]))          # B survives to the end
    s.add(Decide1_A != Decide1_B)  # disagreement

    print("Checking 2-node 2-round for a disagreement counterexample...")
    res = s.check()
    print("Result:", res)

    if res == sat:
        m = s.model()
        print("Counterexample found:")
        print(" initA (True=1):", m.evaluate(initA))
        print(" initB (True=1):", m.evaluate(initB))
        for t in T:
            print(f" C_A_{t}:", m.evaluate(C_A[t]), f" C_B_{t}:", m.evaluate(C_B[t]),
                  f" S_A_{t}:", m.evaluate(S_A[t]), f" S_B_{t}:", m.evaluate(S_B[t]))
        for t in ROUNDS:
            print(f" M_AB_{t}:", m.evaluate(M_AB[t]), f" M_BA_{t}:", m.evaluate(M_BA[t]))
        print(" Decide1_A:", m.evaluate(Decide1_A), " Decide1_B:", m.evaluate(Decide1_B))
    else:
        print("No counterexample. Agreement holds (under these constraints).")

if __name__ == "__main__":
    check_2n2r_receive0()
