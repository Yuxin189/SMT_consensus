"""
Protocol Generator: converts parameter combinations into complete protocol descriptions
"""
from typing import Dict, Optional


class ProtocolGenerator:
    """
    Generates complete protocol descriptions from parameter combinations.
    
    This class takes the synthesized parameters and produces:
    1. Human-readable protocol description
    2. Formal logic formulas
    3. Executable Python code
    4. Protocol name/type identification
    """
    
    def __init__(self, params: Dict[str, bool]):
        """
        Args:
            params: Dict with keys 'keep_old', 'use_incoming', 'use_const_one'
        """
        self.params = params
        self.keep_old = params.get('keep_old', False)
        self.use_incoming = params.get('use_incoming', False)
        self.use_const_one = params.get('use_const_one', False)
    
    def get_protocol_name(self) -> str:
        """Identify the protocol type based on parameters"""
        if self.keep_old and self.use_incoming and not self.use_const_one:
            return "FloodSet (经典洪水集协议)"
        elif self.keep_old and not self.use_incoming and not self.use_const_one:
            return "Static Protocol (状态不变协议)"
        elif not self.keep_old and self.use_incoming and not self.use_const_one:
            return "Incoming-Only Protocol (仅接收协议)"
        elif self.use_const_one:
            return "Invalid Protocol (无效协议 - 会违反规范)"
        else:
            return "Custom Protocol (自定义协议)"
    
    def get_state_update_formula(self) -> str:
        """Generate formal logic formula for state update"""
        terms = []
        
        if self.keep_old:
            terms.append("S[i][t-1]")
        
        if self.use_incoming:
            terms.append("∃j≠i: M(j→i, t) ∧ S[j][t-1]")
        
        if self.use_const_one:
            terms.append("True")
        
        if not terms:
            return "S[i][t] = False"
        
        formula = "S[i][t] = " + " ∨ ".join(terms)
        return formula
    
    def get_state_update_description(self) -> str:
        """Generate human-readable description"""
        parts = []
        
        if self.keep_old:
            parts.append("保留上一轮的状态 S[i][t-1]")
        
        if self.use_incoming:
            parts.append("接收其他节点发送的状态（如果收到任何节点 j 的状态 S[j][t-1]，则更新）")
        
        if self.use_const_one:
            parts.append("无条件设置为 True（这会导致协议无效）")
        
        if not parts:
            return "状态始终为 False（无效协议）"
        
        desc = "节点 i 在第 t 轮的状态 S[i][t] 更新规则：\n"
        desc += "  - " + "\n  - ".join(parts)
        return desc
    
    def get_decision_rule(self) -> str:
        """Get the decision rule"""
        return "决策规则：如果 S[i][R] = True（收到过 0），则决定 0；否则决定 1"
    
    def generate_python_code(self, function_name: str = "synthesized_protocol") -> str:
        """
        Generate executable Python code for the protocol
        
        ═══════════════════════════════════════════════════════════════
        🔑 协议代码生成的位置！
        将找到的参数组合转换为可执行的 Python 代码
        ═══════════════════════════════════════════════════════════════
        
        Returns:
            String containing Python function code
        """
        code = f"""def {function_name}(N: int, R: int):
    '''
    生成的共识协议实现
    
    参数:
        N: 节点数量
        R: 轮数
    
    协议逻辑:
        {self.get_state_update_formula()}
    '''
    from z3 import *
    
    nodes = list(range(1, N + 1))
    T = list(range(R + 1))
    ROUNDS = list(range(1, R + 1))
    
    # 初始化变量
    init = {{i: Bool(f"init_{{i}}") for i in nodes}}
    C = {{i: {{t: Bool(f"C_{{i}}_{{t}}") for t in T}} for i in nodes}}
    M = {{
        (sender, receiver, t): Bool(f"M_{{sender}}_{{receiver}}_{{t}}")
        for sender in nodes
        for receiver in nodes
        if sender != receiver
        for t in ROUNDS
    }}
    S = {{i: {{t: Bool(f"S_{{i}}_{{t}}") for t in T}} for i in nodes}}
    
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
"""
        
        if self.keep_old:
            code += "            terms.append(S[i][t - 1])\n"
        
        if self.use_incoming:
            code += "            terms.append(incoming_any)\n"
        
        if self.use_const_one:
            code += "            terms.append(True)\n"
        
        code += """            
            if terms:
                s.add(S[i][t] == Or(terms))
            else:
                s.add(S[i][t] == False)
    
    # 决策规则
    Decide1 = {i: Bool(f"Decide1_{i}") for i in nodes}
    for i in nodes:
        s.add(Decide1[i] == Not(S[i][R]))
    
    return s, nodes, init, C, M, S, Decide1
"""
        return code
    
    def generate_full_description(self) -> str:
        """Generate complete protocol description"""
        desc = f"""
{'='*70}
生成的共识协议
{'='*70}

协议名称: {self.get_protocol_name()}

参数配置:
  - keep_old     = {self.keep_old}
  - use_incoming = {self.use_incoming}
  - use_const_one = {self.use_const_one}

状态更新公式:
  {self.get_state_update_formula()}

状态更新规则描述:
{self.get_state_update_description()}

{self.get_decision_rule()}

{'='*70}
"""
        return desc
    
    def save_to_file(self, filename: str):
        """Save protocol code to a Python file"""
        code = self.generate_python_code()
        with open(filename, 'w', encoding='utf-8') as f:
            f.write(f"# 自动生成的共识协议代码\n")
            f.write(f"# 协议名称: {self.get_protocol_name()}\n")
            f.write(f"# 状态更新公式: {self.get_state_update_formula()}\n")
            f.write(f"#\n")
            f.write(code)
        print(f"协议代码已保存到: {filename}")
