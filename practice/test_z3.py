from z3 import *

x = Int('x')
s = Solver()
s.add(x > 5, x < 3)
print(s.check())
