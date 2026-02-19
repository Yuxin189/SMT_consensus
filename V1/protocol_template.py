from z3 import *

NODES = [1, 2, 3]
R = 3
T = [0, 1, 2, 3]
ROUNDS = [1, 2, 3]
# 3个节点，每人发0或1，总共 2^3 = 8 种观测组合
OBS = list(range(8)) 

class ProtocolTemplate:
    def __init__(self, K: int, prefix: str = "", ctx: Context = None):
        self.K = K
        self.prefix = prefix
        self.ctx = ctx if ctx is not None else Context()

        self.St, self.qs = EnumSort(f"{prefix}St", [f"{prefix}q{i}" for i in range(K)], ctx=self.ctx)
        
        self.send_rule = Function(f"{prefix}send_rule", self.St, BoolSort(ctx=self.ctx))
        # 输入：当前状态(St)，观测到的位向量整数(0-7)，输出：新状态(St)
        self.update_rule = Function(f"{prefix}update_rule", self.St, IntSort(ctx=self.ctx), self.St)
        self.dec_rule = Function(f"{prefix}dec_rule", self.St, BoolSort(ctx=self.ctx))

    def init_to_state(self, init_bool):
        return If(init_bool, self.qs[1], self.qs[0])

    def iter_table_points(self):
        for q in self.qs:
            yield ("send", (q,))
            yield ("dec", (q,))
            for o in OBS:
                yield ("upd", (q, o))