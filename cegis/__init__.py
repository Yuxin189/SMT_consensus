"""
CEGIS (Counterexample-Guided Inductive Synthesis) Framework
for Consensus Protocol Synthesis

This package implements the CEGIS loop as shown in the diagram:
- Synthesizer: proposes candidate protocol solutions
- Verifier: checks if solutions satisfy specifications
- Counterexample feedback: guides synthesis refinement
"""

from .synthesizer import Synthesizer
from .verifier import Verifier
from .cegis_loop import CEGISLoop
from .protocol_template import ProtocolTemplate

__all__ = ['Synthesizer', 'Verifier', 'CEGISLoop', 'ProtocolTemplate']

