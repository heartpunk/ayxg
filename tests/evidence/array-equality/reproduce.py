"""Standalone Z3 reproducer: no AYXG imports."""
import z3
index = z3.BitVecSort(4)
left = z3.K(index, z3.BitVecVal(0, 1))
right = z3.K(index, z3.BitVecVal(1, 1))
for i in [2, 3, 4, 5, 6, 10, 11]:
    left = z3.Store(left, z3.BitVecVal(i, 4), z3.BitVecVal(1, 1))
for i in [0, 1, 7, 9, 12, 13, 14, 15]:
    right = z3.Store(right, z3.BitVecVal(i, 4), z3.BitVecVal(0, 1))
witness = z3.BitVecVal(8, 4)
solver = z3.Solver()
solver.add(left == right)
print('version:', z3.get_version_string())
print('left[8]:', z3.simplify(z3.Select(left, witness)))
print('right[8]:', z3.simplify(z3.Select(right, witness)))
print('equality:', solver.check())
print(solver.to_smt2())
