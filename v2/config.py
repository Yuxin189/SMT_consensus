"""
========== Part 1: 全局参数 ==========
换节点数、轮数、或消息取值时只改本文件。
"""
import itertools

NUM_NODES = 5
NUM_ROUNDS = 5

# Message values: 0/1 received, 2 = missing
INPUT_PATTERNS = list(itertools.product([0, 1, 2], repeat=NUM_NODES))