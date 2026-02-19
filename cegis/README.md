# CEGIS Consensus Protocol Synthesis

This directory contains a modular implementation of the **Counterexample-Guided Inductive Synthesis (CEGIS)** framework for synthesizing consensus protocols.

## Architecture

The implementation follows the CEGIS diagram structure:

```
Synthesizer ←→ Verifier
     ↓            ↓
  Propose    Verify Spec
     ↓            ↓
  Learn from Counterexamples
     ↓
  Build Constraints
     ↓
  Generate New Solution
```

## Files

- **`protocol_template.py`**: Defines the parameterized protocol template
  - Protocol parameters as Z3 variables
  - State update logic template

- **`synthesizer.py`**: Synthesizer component
  - Proposes candidate solutions
  - Accumulates counterexamples
  - Builds constraints to avoid known failures

- **`verifier.py`**: Verifier component
  - Verifies if candidate protocol satisfies specifications
  - Finds counterexamples when violations occur
  - Checks: All-0 Validity, All-1 Validity, Agreement

- **`cegis_loop.py`**: Main CEGIS loop orchestrator
  - Coordinates Synthesizer and Verifier
  - Manages iteration until solution found or max iterations

- **`main.py`**: Entry point for running synthesis

## Usage

```bash
# From the project root
cd cegis
python main.py
```

Or import and use programmatically:

```python
from cegis.cegis_loop import CEGISLoop

loop = CEGISLoop(N=4, R=3, max_iterations=10)
result = loop.run()

if result:
    print(f"Found protocol: {result}")
```

## How It Works

1. **Synthesizer** proposes a candidate protocol (assignment to parameters)
2. **Verifier** checks if this protocol satisfies:
   - All-0 Validity: if all inputs are 0, all decisions must be 0
   - All-1 Validity: if all inputs are 1, all decisions must be 1
   - Agreement: all surviving nodes must decide the same value
3. If **counterexample found** (violation exists):
   - Verifier feeds counterexample back to Synthesizer
   - Synthesizer adds constraint to exclude this parameter combination
   - Synthesizer generates new candidate
4. If **no counterexample** found:
   - Protocol is correct! Return solution
5. Repeat until solution found or max iterations

## Protocol Template

The current template has 3 boolean parameters:
- `keep_old`: Whether to keep previous state `S[i][t-1]`
- `use_incoming`: Whether to use incoming messages from other nodes
- `use_const_one`: Whether to allow constant True

State update formula:
```
S[i][t] = (keep_old ∧ S[i][t-1]) 
       ∨ (use_incoming ∧ incoming_messages)
       ∨ (use_const_one ∧ True)
```

## Extending

To extend the template with more parameters or different logic:
1. Modify `ProtocolTemplate` in `protocol_template.py`
2. Update `Synthesizer` to handle new parameters
3. `Verifier` should work automatically with the new template

