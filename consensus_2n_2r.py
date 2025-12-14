from z3 import *

def check_consensus_2n_2r():
    s = Solver()

    # Two nodes: 0, 1
    # Two rounds: 0 (init), 1, 2
    N = 2
    R = 2

    init = [Bool(f"init_{i}") for i in range(N)]
    alive = [[Bool(f"alive_{i}_{r}") for r in range(R + 1)] for i in range(N)]
    seen1 = [[Bool(f"seen1_{i}_{r}") for r in range(R + 1)] for i in range(N)]
    deliver = [[[Bool(f"del_{src}_{dst}_{r}") for r in range(1, R + 1)]
                for dst in range(N)] for src in range(N)]

    # Everyone alive initially
    for i in range(N):
        s.add(alive[i][0] == True)

    # Crash is permanent
    for i in range(N):
        for r in range(1, R + 1):
            s.add(Implies(alive[i][r], alive[i][r - 1]))

    # At least one survivor at the end
    s.add(Or(alive[0][R], alive[1][R]))

    # Delivery rule (synchronous + crash with partial delivery)
    for src in range(N):
        for dst in range(N):
            if src == dst:
                continue
            for r in range(1, R + 1):
                s.add(Implies(
                    And(alive[src][r], alive[dst][r]),
                    deliver[src][dst][r - 1]
                ))

    # Protocol
    for i in range(N):
        s.add(seen1[i][0] == init[i])

    for i in range(N):
        for r in range(1, R + 1):
            s.add(seen1[i][r] ==
                  Or(
                      seen1[i][r - 1],
                      And(deliver[1 - i][i][r - 1], seen1[1 - i][r - 1])
                  ))

    decision = [seen1[i][R] for i in range(N)]

    # Try to violate agreement
    s.add(alive[0][R])
    s.add(alive[1][R])
    s.add(decision[0] != decision[1])

    print("Checking 2-node 2-round consensus...")
    result = s.check()
    print("Result:", result)

    if result == sat:
        print("Counterexample:")
        print(s.model())
    else:
        print("No counterexample. Agreement holds.")

if __name__ == "__main__":
    check_consensus_2n_2r()
