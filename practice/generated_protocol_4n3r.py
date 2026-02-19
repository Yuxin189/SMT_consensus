======================================================================
生成的共识协议
======================================================================

协议名称: FloodSet (经典洪水集协议)

协议参数:
  - keep_old     = True
  - use_incoming = True
  - use_const_one = False

形式化逻辑公式:
  S[i][t] = S[i][t-1] ∨ ∃j≠i: M(j→i, t) ∧ S[j][t-1]

状态更新规则描述:
  节点 i 在第 t 轮的状态 S[i][t] 更新规则：
  - 保留上一轮的状态 S[i][t-1]
  - 接收其他节点发送的状态（如果收到任何节点 j 的状态 S[j][t-1]，则更新）

决策规则：如果 S[i][R] = True（收到过 0），则决定 0；否则决定 1

协议解决的问题:
  这是一个崩溃容错共识协议，保证在异步分布式系统中：
  1. 有效性 (Validity): 如果所有节点初始值都是 v，则所有存活节点必须决定 v
  2. 一致性 (Agreement): 所有存活节点必须决定相同的值
  3. 容错性: 即使部分节点崩溃，协议仍然能达成共识

======================================================================


# ======================================================================
# 生成的协议代码
# ======================================================================

def synthesized_protocol(N: int, R: int):
    """
    生成的共识协议代码
    
    协议类型: FloodSet (经典洪水集协议)
    参数: keep_old=True, use_incoming=True, use_const_one=False
    """
    from z3 import *
    
    s = Solver()
    nodes = list(range(1, N + 1))
    T = list(range(R + 1))
    ROUNDS = list(range(1, R + 1))
    
    # 环境变量
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
                    M[(sender, receiver, t)]
                ))
                s.add(Implies(M[(sender, receiver, t)], Not(C[sender][t - 1])))
                s.add(Implies(M[(sender, receiver, t)], Not(C[receiver][t])))
    
    # 初始状态
    for i in nodes:
        s.add(S[i][0] == Not(init[i]))
    
    # === 协议状态更新逻辑（这是生成的部分）===
    # 状态更新规则:
    # S[i][t] = S[i][t-1] ∨ ∃j≠i: M(j→i, t) ∧ S[j][t-1]
    for i in nodes:
        for t in ROUNDS:
            incoming = [And(M[(j, i, t)], S[j][t - 1]) for j in nodes if j != i]
            incoming_any = Or(incoming) if incoming else False
            
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
    
    return s, nodes, T, ROUNDS, init, C, M, S, Decide1
