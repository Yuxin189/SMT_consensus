# 自动生成的共识协议代码
# 协议名称: FloodSet (经典洪水集协议)
# 状态更新公式: S[i][t] = S[i][t-1] ∨ ∃j≠i: M(j→i, t) ∧ S[j][t-1]
#
def synthesized_protocol(N: int, R: int):
    '''
    生成的共识协议实现
    
    参数:
        N: 节点数量
        R: 轮数
    
    协议逻辑:
        S[i][t] = S[i][t-1] ∨ ∃j≠i: M(j→i, t) ∧ S[j][t-1]
    '''
    from z3 import *
    
    nodes = list(range(1, N + 1))
    T = list(range(R + 1))
    ROUNDS = list(range(1, R + 1))
    
    # 初始化变量
    init = {i: Bool(f"init_{i}") for i in nodes}
    C = {i: {t: Bool(f"C_{i}_{t}") for t in T} for i in nodes}
    M = {
        (sender, receiver, t): Bool(f"M_{sender}_{receiver}_{t}")
        for sender in nodes
        for receiver in nodes
        if sender != receiver
        for t in ROUNDS
    }
    S = {i: {t: Bool(f"S_{i}_{t}") for t in T} for i in nodes}
    
    s = Solver()
    
    # 环境约束（崩溃、消息传递等）
    for i in nodes:
        s.add(C[i][0] == False)
    for i in nodes:
        for t in range(R):
            s.add(Implies(C[i][t], C[i][t + 1]))
    s.add(Or([Not(C[i][R]) for i in nodes]))
    
    for sender in nodes:
        for receiver in nodes:
            if sender == receiver:
                continue
            for t in ROUNDS:
                s.add(Implies(
                    And(Not(C[sender][t]), Not(C[receiver][t])),
                    M[(sender, receiver, t)],
                ))
                s.add(Implies(M[(sender, receiver, t)], Not(C[sender][t - 1])))
                s.add(Implies(M[(sender, receiver, t)], Not(C[receiver][t])))
    
    # 初始状态
    for i in nodes:
        s.add(S[i][0] == Not(init[i]))
    
    # 协议状态更新规则（这是生成的核心部分）
    for i in nodes:
        for t in ROUNDS:
            incoming = [
                And(M[(j, i, t)], S[j][t - 1]) 
                for j in nodes if j != i
            ]
            incoming_any = Or(incoming) if incoming else False
            
            # 生成的状态更新逻辑
            terms = []
            terms.append(S[i][t - 1])
            terms.append(incoming_any)
            
            if terms:
                s.add(S[i][t] == Or(terms))
            else:
                s.add(S[i][t] == False)
    
    # 决策规则
    Decide1 = {i: Bool(f"Decide1_{i}") for i in nodes}
    for i in nodes:
        s.add(Decide1[i] == Not(S[i][R]))
    
    return s, nodes, init, C, M, S, Decide1
