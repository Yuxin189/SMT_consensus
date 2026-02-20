"""
========== Part 1: Global parameters ==========
Change this file only when changing node count, round count, or message values.
"""
import itertools

NUM_NODES = 3
NUM_ROUNDS = 3

# Message values: 0/1 received, 2 = missing
INPUT_PATTERNS = list(itertools.product([0, 1, 2], repeat=NUM_NODES))