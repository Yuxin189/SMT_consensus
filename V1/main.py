# main.py
from protocol_template import NODES, R, T, ROUNDS
from synthesizer import synthesize
from verifier import find_counterexample

def seed_scenario_all_delivered(all_one: bool):
    return {
        "init": {i: all_one for i in NODES},
        "C": {i: {t: False for t in T} for i in NODES},
        "M": {(s, r, t): True for s in NODES for r in NODES if s != r for t in ROUNDS},
    }

def pretty_summary(sc):
    print("init:", sc["init"])
    print("crash_end:", {i: sc["C"][i][R] for i in NODES})
    for t in ROUNDS:
        delivered = [f"{a}->{b}" for (a,b,tt),v in sc["M"].items() if tt==t and v]
        print(f"round {t} delivered:", delivered if delivered else "(none)")

def scenario_key(sc):
    """Generate a unique key for a scenario to avoid duplicates"""
    init_key = tuple(sorted(sc["init"].items()))
    C_key = tuple((i, tuple(sorted(sc["C"][i].items()))) for i in sorted(sc["C"].keys()))
    M_key = tuple(sorted(sc["M"].items()))
    return (init_key, C_key, M_key)

def main():
    K = 3
    CE = []
    seen_scenarios = set()

    # seed so SYN isn't completely unconstrained
    seed0 = seed_scenario_all_delivered(all_one=False)
    seed1 = seed_scenario_all_delivered(all_one=True)
    CE.append(seed0)
    CE.append(seed1)
    seen_scenarios.add(scenario_key(seed0))
    seen_scenarios.add(scenario_key(seed1))

    it = 0
    while True:
        print(f"\n================ Iter {it}: SYN ================")
        ok, tables, _ = synthesize(CE, K=K)
        if not ok:
            print("SYN UNSAT: no protocol fits accumulated counterexamples.")
            print(f"Total counterexamples accumulated: {len(CE)}")
            return

        print("Candidate protocol tables:")
        print("  send:", tables["send"])
        print("  dec :", tables["dec"])
        some_upd = list(tables["upd"].items())[:12]
        print("  upd (first 12):", some_upd)

        print(f"\n---------------- Iter {it}: VER ----------------")
        found, cex = find_counterexample(tables, K=K)
        if not found:
            print("✅ SUCCESS: verifier found no counterexample (within model).")
            print("Final protocol:")
            print("  send:", tables["send"])
            print("  dec :", tables["dec"])
            print("  upd :", tables["upd"])
            print(f"Total iterations: {it}, Total counterexamples: {len(CE)}")
            return

        cex_key = scenario_key(cex)
        if cex_key in seen_scenarios:
            print("⚠️  Duplicate counterexample detected, skipping...")
            print("This suggests the synthesizer cannot avoid this scenario with current constraints.")
            print("Consider increasing K (state space) or checking specification.")
            # Still try to continue, but this is a warning
        else:
            print("❌ Counterexample found, adding to CE:")
            pretty_summary(cex)
            CE.append(cex)
            seen_scenarios.add(cex_key)
        
        it += 1
        if it % 50 == 0:
            print(f"\n[Progress] Iteration {it}, {len(CE)} unique counterexamples")

if __name__ == "__main__":
    main()
