"""
========== Part 2: 协议执行语义 ==========
给定 init / alive / loss 和 SM 表，构建多轮状态迹 S[r][i]。
若以后要换一种 protocol 执行方式（例如不同消息模型），只改本文件。
"""
from z3 import *
from config import NUM_NODES, NUM_ROUNDS, INPUT_PATTERNS


def build_execution_trace(solver, sm_logic, init_vals, alive_vals, loss_vals, trace_name_suffix=""):
    """
    alive_vals[r][i]: True if node i is alive at start of round r+1 (r=0..NUM_ROUNDS-1)
    For r=0: alive at start of round 1
    """
    # ---------- 2.1 状态变量 S[r][i] ----------
    S = [[Int(f"S_r{r}_n{i}_{trace_name_suffix}") for i in range(NUM_NODES)] for r in range(NUM_ROUNDS + 1)]

    # ---------- 2.2 初始状态 (Round 0) ----------
    for i in range(NUM_NODES):
        solver.add(S[0][i] == init_vals[i])

    # ---------- 2.3 每轮更新：收消息 -> SM 查表 -> 新状态（crash-stop 下死节点保持旧状态） ----------
    for r in range(1, NUM_ROUNDS + 1):
        for i in range(NUM_NODES):
            # recv_vec: self always visible if alive; others via loss
            recv_vec = []
            for sender in range(NUM_NODES):
                if sender == i:
                    val = If(alive_vals[r-1][i], S[r-1][i], 2)
                else:
                    delivered = And(alive_vals[r-1][sender], loss_vals[r-1][sender][i])
                    val = If(delivered, S[r-1][sender], 2)
                recv_vec.append(val)

            current_round_rules = sm_logic[r-1]
            last_idx = len(INPUT_PATTERNS) - 1
            nested_expr = current_round_rules[last_idx]

            for p_idx in range(len(INPUT_PATTERNS) - 2, -1, -1):
                pattern = INPUT_PATTERNS[p_idx]
                rule_val = current_round_rules[p_idx]
                match_conds = [recv_vec[k] == pattern[k] for k in range(NUM_NODES)]
                match = And(match_conds)
                nested_expr = If(match, rule_val, nested_expr)

            # crash-stop: if not alive at round r start, freeze state
            new_state = nested_expr
            solver.add(S[r][i] == If(alive_vals[r-1][i], new_state, S[r-1][i]))

    return S
