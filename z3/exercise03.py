from z3 import *

P, Q, R = Bools('P Q R')

print("Exercise 03 a)")

exercise03A = Solver()
exercise03A.add(Not(Not(P)) == P)

print(exercise03A.check())
print("Model:", exercise03A.model())


print("Exercise 03 b)")

exercise03B = Solver()
exercise03B.add(And(Not(P), And(Or(P, Q), Not(Q))))

print(exercise03B.check())

print("Exercise 03 c)")

exercise03CFormula = Implies(And(P, Q), R) == Implies(P, Implies(Q, R))

exercise03C = Solver()
exercise03C.add(Not(exercise03CFormula))

print("tauto" if exercise03C.check() == unsat else "not a tautology")

