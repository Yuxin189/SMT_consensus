from z3 import *
from protocol_template import ProtocolTemplate, NODES, R, T, ROUNDS

def add_failure_model(s, C, M):
    for i in NODES:
        s.add(C[i][0] == False)
        for t in range(R):
            s.add(Implies(C[i][t], C[i][t+1]))
    s.add(Or([Not(C[i][R]) for i in NODES]))
    for t in ROUNDS:
        for sender in NODES:
            for receiver in NODES:
                if sender == receiver: continue
                s.add(Implies(M[(sender, receiver, t)], Not(C[sender][t-1])))
                s.add(Implies(M[(sender, receiver, t)], Not(C[receiver][t])))
                s.add(Implies(And(Not(C[sender][t]), Not(C[receiver][t])), M[(sender, receiver, t)]))

def find_counterexample(tables, K=6):
    ctx = Context()
    s = Solver(ctx=ctx)
    init = {i: Bool(f"init_{i}", ctx=ctx) for i in NODES}
    C = {i: {t: Bool(f"C_{i}_{t}", ctx=ctx) for t in T} for i in NODES}
    M = {(s, r, t): Bool(f"M_{s}_{r}_{t}", ctx=ctx) for s in NODES for r in NODES if s!=r for t in ROUNDS}

    add_failure_model(s, C, M)

    tmpl = ProtocolTemplate(K=K, prefix="syn_", ctx=ctx)
    qmap = {q.decl().name(): q for q in tmpl.qs}

    for qn, b in tables["send"].items(): s.add(tmpl.send_rule(qmap[qn]) == (b==1))
    for qn, b in tables["dec"].items(): s.add(tmpl.dec_rule(qmap[qn]) == (b==1))
    for (qn, o), qnxt in tables["upd"].items(): s.add(tmpl.update_rule(qmap[qn], IntVal(o, ctx)) == qmap[qnxt])

    st = {i: {t: Const(f"st_i{i}_t{t}", tmpl.St) for t in T} for i in NODES}
    for i in NODES:
        s.add(st[i][0] == tmpl.init_to_state(init[i]))
        for t in ROUNDS:
            # 这里的 M 是 Variable，由 Verifier 寻找
            from synthesizer import get_obs_vector
            obs_vec = get_obs_vector(tmpl, {idx: st[idx][t-1] for idx in NODES}, i, t, M, False)
            s.add(st[i][t] == If(C[i][t-1], st[i][t-1], tmpl.update_rule(st[i][t-1], obs_vec)))

    alive = {i: Not(C[i][R]) for i in NODES}
    dec1 = {i: tmpl.dec_rule(st[i][R]) for i in NODES}
    ag_vio = Or([And(alive[a], alive[b], dec1[a] != dec1[b]) for a in NODES for b in NODES if a < b])
    all0, all1 = And([Not(init[i]) for i in NODES]), And([init[i] for i in NODES])
    val_vio = Or(And(all0, Or([And(alive[i], dec1[i]) for i in NODES])),
                 And(all1, Or([And(alive[i], Not(dec1[i])) for i in NODES])))

    s.add(Or(ag_vio, val_vio))
    if s.check() != sat: return False, None
    m = s.model()
    return True, {
        "init": {i: is_true(m.eval(init[i], True)) for i in NODES},
        "C": {i: {t: is_true(m.eval(C[i][t], True)) for t in T} for i in NODES},
        "M": {k: is_true(m.eval(v, True)) for k,v in M.items()}
    }