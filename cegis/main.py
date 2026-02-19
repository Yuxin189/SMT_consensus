"""
Main entry point for CEGIS consensus protocol synthesis
"""
from .cegis_loop import CEGISLoop


def main():
    """Main function to run CEGIS synthesis"""
    print("=" * 70)
    print("CEGIS Consensus Protocol Synthesis")
    print("=" * 70)
    print()
    
    # Example: synthesize for small scale first
    print("Example 1: Small scale (N=4, R=3)")
    print("-" * 70)
    loop1 = CEGISLoop(N=4, R=3, max_iterations=10)
    result1 = loop1.run(save_to_file="generated_protocol_4n3r.py")
    
    if result1:
        print("\n✓ Synthesis successful! Protocol saved to generated_protocol_4n3r.py")
    else:
        print("\n✗ Synthesis failed or incomplete")
    
    print("\n" + "=" * 70)
    print()
    
    # Example: try slightly larger scale
    print("Example 2: Medium scale (N=5, R=4)")
    print("-" * 70)
    loop2 = CEGISLoop(N=5, R=4, max_iterations=10)
    result2 = loop2.run(save_to_file="generated_protocol_5n4r.py")
    
    if result2:
        print("\n✓ Synthesis successful! Protocol saved to generated_protocol_5n4r.py")
    else:
        print("\n✗ Synthesis failed or incomplete")


if __name__ == "__main__":
    main()

