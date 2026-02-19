"""
Synthesizer: proposes candidate protocol solutions and learns from counterexamples
"""
from z3 import *
from typing import Optional, Dict, List


class Synthesizer:
    """
    Synthesizer component: generates candidate protocol solutions.
    
    According to the CEGIS diagram:
    - Proposes candidate solutions (assignments to protocol parameters)
    - Accumulates counterexamples from Verifier
    - Constructs SAT scenarios from counterexamples
    - Builds constraints (highlighted in red) to avoid known failures
    - Generates new solutions that satisfy accumulated constraints
    """
    
    def __init__(self, protocol_template):
        """
        Args:
            protocol_template: ProtocolTemplate instance
        """
        self.template = protocol_template
        self.solver = Solver()
        self.counterexamples = []  # Accumulated counterexamples
        
        # Get protocol parameters
        params = protocol_template.get_parameters()
        self.keep_old = params['keep_old']
        self.use_incoming = params['use_incoming']
        self.use_const_one = params['use_const_one']
    
    def propose_candidate(self) -> Optional[Dict[str, bool]]:
        """
        Propose a candidate solution (assignment to protocol parameters).
        
        ═══════════════════════════════════════════════════════════════
        🔑 协议参数搜索的位置！
        Z3 在这里自动搜索满足约束的参数组合
        ═══════════════════════════════════════════════════════════════
        
        Returns:
            Dict mapping parameter names to bool values, or None if no solution exists
        """
        if self.solver.check() == unsat:
            return None
        
        # ⭐ 这里！Z3 求解器找到一个满足所有约束的参数组合
        # 这个组合会被送到 Verifier 去验证
        model = self.solver.model()
        
        def z3_bool_to_python(z3_val):
            if is_true(z3_val):
                return True
            elif is_false(z3_val):
                return False
            else:
                return bool(z3_val)
        
        candidate = {
            'keep_old': z3_bool_to_python(model.evaluate(self.keep_old, model_completion=True)),
            'use_incoming': z3_bool_to_python(model.evaluate(self.use_incoming, model_completion=True)),
            'use_const_one': z3_bool_to_python(model.evaluate(self.use_const_one, model_completion=True)),
        }
        
        return candidate
    
    def accumulate_counterexample(self, counterexample, candidate_params: Dict[str, bool]):
        """
        Accumulate a counterexample and build constraints.
        
        According to the diagram:
        - "Accumulate counterexamples"
        - "Construct SAT scenarios" 
        - "Build constraints" (highlighted in red)
        
        Args:
            counterexample: Counterexample object from Verifier
            candidate_params: The candidate parameters that led to this counterexample
        """
        self.counterexamples.append(counterexample)
        
        # Build constraint: exclude this parameter combination
        # This ensures future candidates avoid this known failure
        exclude_constraint = Not(And(
            self.keep_old == candidate_params['keep_old'],
            self.use_incoming == candidate_params['use_incoming'],
            self.use_const_one == candidate_params['use_const_one'],
        ))
        
        self.solver.add(exclude_constraint)
    
    def get_constraint_count(self) -> int:
        """Return number of accumulated constraints"""
        return len(self.solver.assertions())
    
    def get_counterexample_count(self) -> int:
        """Return number of accumulated counterexamples"""
        return len(self.counterexamples)

