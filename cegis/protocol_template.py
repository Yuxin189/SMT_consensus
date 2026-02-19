"""
Protocol Template: defines the parameterized protocol logic
"""
from z3 import *


class ProtocolTemplate:
    """
    Defines a parameterized template for consensus protocols.
    
    The template allows Z3 to search for protocol parameters that
    satisfy the consensus specification.
    """
    
    def __init__(self):
        # Protocol parameters as Z3 variables
        self.keep_old = Bool("keep_old")      # Keep previous state?
        self.use_incoming = Bool("use_incoming")  # Use incoming messages?
        self.use_const_one = Bool("use_const_one")  # Allow constant True?
    
    def get_parameters(self):
        """Return all protocol parameters as a dict"""
        return {
            'keep_old': self.keep_old,
            'use_incoming': self.use_incoming,
            'use_const_one': self.use_const_one,
        }
    
    def build_state_update(self, S_prev, incoming_any):
        """
        Build the state update formula: S[i][t] = f(S[i][t-1], incoming)
        
        ═══════════════════════════════════════════════════════════════
        🔑 协议模板定义的位置！
        这里定义了参数化的协议逻辑
        ═══════════════════════════════════════════════════════════════
        
        Args:
            S_prev: S[i][t-1] - previous state
            incoming_any: OR of all incoming messages with their states
        
        Returns:
            Z3 formula for S[i][t]
        """
        terms = []
        
        # ⭐ 根据参数决定是否包含各项，生成参数化的协议逻辑
        # 当参数是 Z3 变量时：生成 If-then-else 表达式
        # 当参数是具体值时：生成具体的公式（如 S[i][t-1] ∨ incoming_any）
        
        # If keep_old is True, include S[i][t-1], else False
        terms.append(If(self.keep_old, S_prev, False))
        
        # If use_incoming is True, include incoming_any, else False
        terms.append(If(self.use_incoming, incoming_any, False))
        
        # If use_const_one is True, include True, else False
        terms.append(If(self.use_const_one, True, False))
        
        # S[i][t] = any of the enabled terms
        return Or(terms)
    
    def instantiate_with_values(self, keep_old_val: bool, use_incoming_val: bool, 
                                use_const_one_val: bool):
        """
        Create constraints that fix parameters to specific values.
        Used when Verifier needs to check a specific candidate.
        
        Returns:
            List of Z3 constraints
        """
        return [
            self.keep_old == keep_old_val,
            self.use_incoming == use_incoming_val,
            self.use_const_one == use_const_one_val,
        ]

