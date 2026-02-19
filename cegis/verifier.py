"""
Verifier: checks if a candidate protocol satisfies the specification
"""
from z3 import *
from typing import Optional, Dict, Tuple, List


class Counterexample:
    """Represents a counterexample found by the verifier"""
    def __init__(self, ce_type: str, model: Model, nodes: List[int], R_final: int,
                 init: Dict, C: Dict, Decide1: Dict):
        self.type = ce_type  # 'all_0_validity', 'all_1_validity', or 'agreement'
        self.model = model
        self.nodes = nodes
        self.R_final = R_final
        self.init = init
        self.C = C
        self.Decide1 = Decide1
    
    def __str__(self):
        return f"Counterexample(type={self.type})"


class Verifier:
    """
    Verifier component: verifies if a candidate protocol satisfies specifications.
    
    According to the CEGIS diagram:
    - Receives a candidate solution from Synthesizer
    - Verifies specification (Validity + Agreement)
    - If violation found (UNSAT path): finds counterexample and feeds back
    - If no violation (SAT): solution is provisionally valid
    """
    
    def __init__(self, N: int, R: int):
        self.N = N
        self.R = R
        self.nodes = list(range(1, N + 1))
        self.T = list(range(R + 1))
        self.ROUNDS = list(range(1, R + 1))
        self.R_final = R
    
    def build_environment(self, protocol_template, protocol_params_fixed=None):
        """
        Build the consensus environment with protocol logic.
        
        Args:
            protocol_template: ProtocolTemplate instance
            protocol_params_fixed: Optional dict of {param_name: bool_value}
                                  to fix parameters to specific values
        
        Returns:
            (solver, init, C, M, S, Decide1)
        """
        s = Solver()
        
        # Environment variables
        init = {i: Bool(f"init_{i}") for i in self.nodes}
        C = {i: {t: Bool(f"C_{i}_{t}") for t in self.T} for i in self.nodes}
        M = {
            (sender, receiver, t): Bool(f"M_{sender}_{receiver}_{t}")
            for sender in self.nodes
            for receiver in self.nodes
            if sender != receiver
            for t in self.ROUNDS
        }
        S = {i: {t: Bool(f"S_{i}_{t}") for t in self.T} for i in self.nodes}
        
        # Environment constraints
        # 1. All nodes survive initially
        for i in self.nodes:
            s.add(C[i][0] == False)
        
        # 2. Crash persistence: C(t) -> C(t+1)
        for i in self.nodes:
            for t in range(self.R):
                s.add(Implies(C[i][t], C[i][t + 1]))
        
        # 3. At least one node survives
        s.add(Or([Not(C[i][self.R_final]) for i in self.nodes]))
        
        # 4. Message delivery constraints
        for sender in self.nodes:
            for receiver in self.nodes:
                if sender == receiver:
                    continue
                for t in self.ROUNDS:
                    # Reliability: both alive -> message delivered
                    s.add(
                        Implies(
                            And(Not(C[sender][t]), Not(C[receiver][t])),
                            M[(sender, receiver, t)],
                        )
                    )
                    # Delivery implies sender alive at start
                    s.add(Implies(M[(sender, receiver, t)], Not(C[sender][t - 1])))
                    # Delivery implies receiver alive at end
                    s.add(Implies(M[(sender, receiver, t)], Not(C[receiver][t])))
        
        # 5. Initial state
        for i in self.nodes:
            s.add(S[i][0] == Not(init[i]))
        
        # 6. Protocol state updates (using template)
        # ═══════════════════════════════════════════════════════════════
        # 🔑 协议生成的核心位置！
        # 这里将参数化的模板实例化为具体的协议逻辑
        # ═══════════════════════════════════════════════════════════════
        for i in self.nodes:
            for t in self.ROUNDS:
                incoming = [
                    And(M[(j, i, t)], S[j][t - 1]) 
                    for j in self.nodes if j != i
                ]
                incoming_any = Or(incoming) if incoming else False
                
                # ⭐ 这里！协议逻辑在这里生成！
                # protocol_template.build_state_update() 根据参数生成：
                # - 如果 keep_old=True, use_incoming=True: S[i][t] = S[i][t-1] ∨ incoming_any
                # - 如果 keep_old=False, use_incoming=True: S[i][t] = incoming_any
                # - 等等...
                s.add(S[i][t] == protocol_template.build_state_update(S[i][t - 1], incoming_any))
        
        # 7. Decision: decide 0 iff received 0, else decide 1
        Decide1 = {i: Bool(f"Decide1_{i}") for i in self.nodes}
        for i in self.nodes:
            s.add(Decide1[i] == Not(S[i][self.R_final]))
        
        # 8. Fix protocol parameters if provided
        if protocol_params_fixed:
            params = protocol_template.get_parameters()
            for param_name, param_value in protocol_params_fixed.items():
                if param_name in params:
                    s.add(params[param_name] == param_value)
        
        return s, init, C, M, S, Decide1
    
    def verify_specification(self, protocol_template, protocol_params: Dict[str, bool]) -> Optional[Counterexample]:
        """
        Verify if the candidate protocol satisfies all specifications.
        
        Args:
            protocol_template: ProtocolTemplate instance
            protocol_params: Dict mapping parameter names to bool values
        
        Returns:
            Counterexample if violation found, None if specification satisfied
        """
        s, init, C, M, S, Decide1 = self.build_environment(
            protocol_template, protocol_params_fixed=protocol_params
        )
        
        # Check 1: All-0 Validity
        s.push()
        s.add(And([Not(init[i]) for i in self.nodes]))
        violation_all_0 = Or([
            And(Not(C[i][self.R_final]), Decide1[i]) 
            for i in self.nodes
        ])
        s.add(violation_all_0)
        if s.check() == sat:
            m = s.model()
            s.pop()
            return Counterexample(
                'all_0_validity', m, self.nodes, self.R_final,
                init, C, Decide1
            )
        s.pop()
        
        # Check 2: All-1 Validity
        s.push()
        s.add(And([init[i] for i in self.nodes]))
        violation_all_1 = Or([
            And(Not(C[i][self.R_final]), Not(Decide1[i])) 
            for i in self.nodes
        ])
        s.add(violation_all_1)
        if s.check() == sat:
            m = s.model()
            s.pop()
            return Counterexample(
                'all_1_validity', m, self.nodes, self.R_final,
                init, C, Decide1
            )
        s.pop()
        
        # Check 3: Agreement
        s.push()
        disagreements = []
        for i in self.nodes:
            for j in self.nodes:
                if i < j:
                    disagreements.append(
                        And(
                            Not(C[i][self.R_final]),
                            Not(C[j][self.R_final]),
                            Decide1[i] != Decide1[j],
                        )
                    )
        s.add(Or(disagreements))
        if s.check() == sat:
            m = s.model()
            s.pop()
            return Counterexample(
                'agreement', m, self.nodes, self.R_final,
                init, C, Decide1
            )
        s.pop()
        
        # No counterexample found - specification satisfied!
        return None

