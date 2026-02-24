# CEGIS v2 — Code layout by parts

| Part | File | Role | When to edit |
|------|------|------|--------------|
| **Part 1** | `config.py` | Global parameters (nodes, rounds, input patterns) | Change node count (3/4/5), rounds, or message values |
| **Part 2** | `system_model.py` | Protocol execution semantics (state trace S, SM lookup, crash-stop) | Change protocol execution or message model |
| **Part 3** | `synthesizer.py` | Synthesis: SM variables + constraints per counterexample | Change correctness definition → edit **block 3.2** (Agreement + Validity) |
| **Part 4** | `verifier.py` | Verification: env vars + trace + violation conditions | Change which violations to check → edit **block 4.4** |
| **Part 5** | `main.py` | CEGIS loop, initial counterexample, output and save on success | Change initial cex or output/save format |

- **Only change correctness**: edit block 3.2 in `synthesizer.py` and block 4.4 in `verifier.py` and keep them consistent.
- **Only change execution semantics**: edit `system_model.py` (Part 2).
- **Only change scale**: edit `config.py` (Part 1).

Run: `python main.py` (requires z3).
