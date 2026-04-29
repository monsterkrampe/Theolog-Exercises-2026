# The solution is heavily inspired by the ones provided by Stephan Mennicke and Florens Förster.

from z3 import *
from itertools import product

SOLVE_TASK_D = True

T = 5
k = 2
heights = range(2,4) if SOLVE_TASK_D else range(1,4)

# s_t_h indicates that at step t we throw with height h
prop_vars = { (t, h): Bool(f"s_{t}_{h}") for t in range(T) for h in heights }  

solver = Solver()

# 1. at least one throw per step
solver.add(And([Or([prop_vars[(t, h)] for h in heights]) for t in range(T)]))

# 2. at most one throw per step
solver.add(And([Not(And(prop_vars[(t, h1)], prop_vars[(t, h2)])) for t in range(T) for h1 in heights for h2 in heights if h1 != h2]))

# 3. First condition from exercise (only one catch at each step)
solver.add(And([Not(And(prop_vars[(t1, h1)], prop_vars[(t2, h2)])) for t1 in range(T) for t2 in range(t1+1, T) for h1 in heights for h2 in heights if (t1 + h1) % T == (t2 + h2) % T]))

# 4. Second condition from exercise (average height equals ball count)
height_combinations = filter(lambda hs: sum(hs) == k*T, product(heights, repeat = T))
solver.add(Or([And([prop_vars[(t, hs[t])] for t in range(T)]) for hs in height_combinations]))

# for task d 
if SOLVE_TASK_D:
    solver.add(prop_vars[(0, 3)])

# enumerate all models
models = []
while solver.check() == sat:
    m = solver.model()
    models.append(m)
    solver.add(Not(And([prop_vars[(t, h)] for t in range(T) for h in heights if m[prop_vars[(t, h)]]])))

print(f"{len(models)} Patterns.")

for m in models:
    pattern = [h for t in range(T) for h in heights if m[prop_vars[(t, h)]]]
    print(pattern)

