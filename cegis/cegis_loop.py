"""
CEGIS Loop: orchestrates the interaction between Synthesizer and Verifier
"""
from typing import Optional, Dict, Tuple
from .synthesizer import Synthesizer
from .verifier import Verifier
from .protocol_template import ProtocolTemplate
from .protocol_generator import ProtocolGenerator
from .protocol_generator import ProtocolGenerator


class CEGISLoop:
    """
    Main CEGIS loop that orchestrates the synthesis process.
    
    Follows the diagram:
    1. Synthesizer proposes candidate solution
    2. Verifier verifies specification
    3. If counterexample found: feed back to Synthesizer
    4. Synthesizer builds constraints and generates new solution
    5. Repeat until solution found or max iterations
    """
    
    def __init__(self, N: int, R: int, max_iterations: int = 20):
        """
        Args:
            N: Number of nodes
            R: Number of rounds
            max_iterations: Maximum number of CEGIS iterations
        """
        self.N = N
        self.R = R
        self.max_iterations = max_iterations
        
        # Initialize components
        self.template = ProtocolTemplate()
        self.synthesizer = Synthesizer(self.template)
        self.verifier = Verifier(N, R)
    
    def run(self, save_to_file: Optional[str] = None) -> Optional[Dict[str, bool]]:
        """
        Run the CEGIS loop.
        
        Args:
            save_to_file: Optional filename to save the generated protocol
        
        Returns:
            Dict of protocol parameters if solution found, None otherwise
        """
        print(f"=== CEGIS Synthesis for N={self.N}, R={self.R} ===")
        print(f"Max iterations: {self.max_iterations}\n")
        
        for iteration in range(self.max_iterations):
            print(f"{'='*60}")
            print(f"Iteration {iteration + 1}")
            print(f"{'='*60}")
            
            # STEP 1: Synthesizer proposes candidate solution
            candidate = self.synthesizer.propose_candidate()
            if candidate is None:
                print("[CEGIS] No solution exists in this template family.")
                print("       (All parameter combinations have been excluded)")
                return None
            
            print(f"\n[Synthesizer] Proposing candidate solution:")
            print(f"  keep_old     = {candidate['keep_old']}")
            print(f"  use_incoming = {candidate['use_incoming']}")
            print(f"  use_const_one = {candidate['use_const_one']}")
            print(f"  (Accumulated {self.synthesizer.get_constraint_count()} constraints, "
                  f"{self.synthesizer.get_counterexample_count()} counterexamples)")
            
            # STEP 2: Verifier verifies specification
            print(f"\n[Verifier] Verifying specification...")
            counterexample = self.verifier.verify_specification(
                self.template, candidate
            )
            
            # STEP 3: Check result
            if counterexample is None:
                # No counterexample found - solution is correct!
                print(f"[Verifier] ✓ No counterexample found!")
                print(f"[Verifier] ✓ Specification satisfied for all executions")
                print(f"\n{'='*60}")
                print(f"[CEGIS SUCCESS] Found correct protocol after {iteration + 1} iterations!")
                print(f"{'='*60}")
                
                # Generate complete protocol description
                generator = ProtocolGenerator(candidate)
                print("\n" + generator.generate_full_description())
                
                # Save to file if requested
                if save_to_file:
                    generator.save_protocol(save_to_file)
                
                return candidate
            else:
                # Counterexample found - feed back to Synthesizer
                print(f"[Verifier] ✗ Found counterexample: {counterexample.type}")
                print(f"[Verifier] → Feeding counterexample back to Synthesizer...")
                
                # STEP 4: Synthesizer accumulates counterexample and builds constraints
                self.synthesizer.accumulate_counterexample(counterexample, candidate)
                print(f"[Synthesizer] ✓ Added constraint to avoid this parameter combination")
                print(f"[Synthesizer] → Generating new candidate for next iteration...\n")
        
        # Max iterations reached
        print(f"\n{'='*60}")
        print(f"[CEGIS] Reached max iterations ({self.max_iterations})")
        print(f"       without finding a solution.")
        print(f"{'='*60}")
        return None

