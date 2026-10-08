"""Mutation check: the parametric prover must FIND counterexamples for families known (by brute force) to fail."""
from z3 import Int
from ilp_proof import some_rotation_is_square

k = Int("k")
mutants = {
    "pump run 0 only (0^{k+5}, b fixed)": [k + 5, 2, 0, 0, 0, 4, 0, 0, 1, 0, 0, 0],
    "pump both big gaps by 2k":          [2 * k + 5, 2, 0, 0, 0, 2 * k + 4, 0, 0, 1, 0, 0, 0],
    "b = a (both k+5, shift one zero)":  [k + 5, 2, 0, 0, 0, k + 5, 0, 0, 0, 0, 0, 0],
    "move the lone 0 into gap 2":        [k + 5, 3, 0, 0, 0, k + 4, 0, 0, 0, 0, 0, 0],
}
for name, circ in mutants.items():
    found, info = some_rotation_is_square(circ, extra=[k >= 0])
    print(f"{name:38s} -> {'counterexample k=' + str(info[2][k]) if found else 'UNSAT (mutant NOT caught)'}")
