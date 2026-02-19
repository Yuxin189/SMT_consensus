#!/usr/bin/env python3
"""
Simple script to run CEGIS synthesis
Usage: python run_cegis.py [N] [R] [max_iterations] [output_file]
"""
import sys
import os

# Add parent directory to path for imports
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from cegis.cegis_loop import CEGISLoop
from cegis.protocol_generator import ProtocolGenerator


def main():
    # Default values
    N = 4
    R = 3
    max_iter = 10
    output_file = None
    
    # Parse command line arguments
    if len(sys.argv) > 1:
        N = int(sys.argv[1])
    if len(sys.argv) > 2:
        R = int(sys.argv[2])
    if len(sys.argv) > 3:
        max_iter = int(sys.argv[3])
    if len(sys.argv) > 4:
        output_file = sys.argv[4]
    else:
        output_file = f"generated_protocol_{N}n{R}r.py"
    
    print(f"Running CEGIS synthesis with N={N}, R={R}, max_iterations={max_iter}")
    print(f"Output file: {output_file}")
    print()
    
    loop = CEGISLoop(N=N, R=R, max_iterations=max_iter)
    result = loop.run()
    
    if result:
        generator = ProtocolGenerator(result)
        
        # Save protocol code
        generator.save_to_file(output_file)
        
        print("\n" + "="*70)
        print("FINAL RESULT: Protocol found and saved!")
        print("="*70)
        print(f"Protocol: {generator.get_protocol_name()}")
        print(f"\nState Update Formula:")
        print(f"  {generator.get_state_update_formula()}")
        print(f"\n{generator.get_state_update_description()}")
        print(f"\n{generator.get_decision_rule()}")
        print(f"\n✓ Protocol code saved to: {output_file}")
        print(f"You can now import and use the generated protocol!")
        return 0
    else:
        print("\n" + "="*70)
        print("FINAL RESULT: No protocol found")
        print("="*70)
        return 1


if __name__ == "__main__":
    sys.exit(main())

