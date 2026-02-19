from z3 import *
from protocol_template import ProtocolTemplate, NODES, R, T, ROUNDS

def get_obs_vector(tmpl, st_prev, i, t, M_round, is_syn, sc=None):
    """根据白板逻辑，计算节点 i 观测到的 3 位向量"""
    bits = []
    for j in NODES:
        if j == i:
            # 观察自己发出的位
            bit = tmpl.send_rule(st_prev[j])
        else:
            # 观察别人，需考虑消息是否送达
            if is_syn:
                delivered = BoolVal(sc["M"][(j, i, t)], ctx=tmpl.ctx)
            else:
                delivered = M_round[(j, i, t)]
            bit = And(delivered, tmpl.send_rule(st_prev[j]))
        bits.append(If(bit, 1, 0))
    # 转换为整数: bit_node1 + 2*bit_node2 + 4*bit_node3
    return bits[0] + 2*bits[1] + 4*bits[2]

def synthesize(CE, K=6):
    ctx = Context()
    s = Solver(ctx=ctx)
    tmpl = ProtocolTemplate(K=K, prefix="syn_", ctx=ctx)

    for k, sc in enumerate(CE):
        st = {i: {t: Const(f"st_k{k}_i{i}_t{t}", tmpl.St) for t in T} for i in NODES}
        for i in NODES:
            s.add(st[i][0] == tmpl.init_to_state(BoolVal(sc["init"][i], ctx=ctx)))
            for t in ROUNDS:
                # 场景 sc 中的 M 被视为 Constant
                obs_vec = get_obs_vector(tmpl, {idx: st[idx][t-1] for idx in NODES}, i, t, None, True, sc)
                crashed_prev = BoolVal(sc["C"][i][t-1], ctx=ctx)
                s.add(st[i][t] == If(crashed_prev, st[i][t-1], tmpl.update_rule(st[i][t-1], obs_vec)))

        alive = {i: Not(BoolVal(sc["C"][i][R], ctx=ctx)) for i in NODES}
        dec = {i: tmpl.dec_rule(st[i][R]) for i in NODES}
        for a in NODES:
            for b in NODES:
                if a < b: s.add(Implies(And(alive[a], alive[b]), dec[a] == dec[b]))
        
        # Validity 约束
        all0 = And([Not(BoolVal(sc["init"][i], ctx=ctx)) for i in NODES])
        all1 = And([BoolVal(sc["init"][i], ctx=ctx) for i in NODES])
        for i in NODES:
            s.add(Implies(And(all0, alive[i]), Not(dec[i])))
            s.add(Implies(And(all1, alive[i]), dec[i]))

    if s.check() != sat: return False, None, None
    m = s.model()
    
    # 导出表逻辑
    tables = {"send": {}, "dec": {}, "upd": {}}
    for kind, args in tmpl.iter_table_points():
        qn = args[0].decl().name()
        if kind == "send":
            tables["send"][qn] = 1 if is_true(m.eval(tmpl.send_rule(args[0]), True)) else 0
        elif kind == "dec":
            tables["dec"][qn] = 1 if is_true(m.eval(tmpl.dec_rule(args[0]), True)) else 0
        else:
            qnxt = m.eval(tmpl.update_rule(args[0], IntVal(args[1], ctx)), True).decl().name()
            tables["upd"][(qn, args[1])] = qnxt
    return True, tables, m