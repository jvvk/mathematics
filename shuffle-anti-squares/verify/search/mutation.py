"""Mutation check of the parametric prover in ilp_proof.py.

Negative mutants: families that are NOT anti-squares for some k >= 0. The prover must find a counterexample k, and
brute force (./antisq) must confirm that the word at that k has a shuffle-square rotation.
Positive control: pumping both long gaps by 2k gives W_{2k}, an anti-square for every k; the prover must answer UNSAT.
Exits 1 if any expectation fails, 3 if the solver or ./antisq is inconclusive.
"""
import sys

from z3 import Int, IntVal, simplify, substitute

from ilp_proof import Inconclusive, run_antisq, some_rotation_is_square

k = Int("k")
NEGATIVE = {
    "pump run 0 only (0^{k+5}, b fixed)": [k + 5, 2, 0, 0, 0, 4, 0, 0, 1, 0, 0, 0],
    "b = a (both k+5, shift one zero)": [k + 5, 2, 0, 0, 0, k + 5, 0, 0, 0, 0, 0, 0],
    "move the lone 0 into gap 2": [k + 5, 3, 0, 0, 0, k + 4, 0, 0, 0, 0, 0, 0],
    "move one zero from gap 1 to gap 8": [k + 5, 1, 0, 0, 0, k + 4, 0, 0, 2, 0, 0, 0],
}
POSITIVE = {"control: pump both long gaps by 2k (= W_{2k})": [2 * k + 5, 2, 0, 0, 0, 2 * k + 4, 0, 0, 1, 0, 0, 0]}


def word(circ: list, kv: int) -> str:
    """The circular word with gap circ[j] (evaluated at k = kv) before its j-th one."""
    gaps = [g if isinstance(g, int) else simplify(substitute(g, (k, IntVal(kv)))).as_long() for g in circ]
    return "".join("0" * g + "1" for g in gaps)


ok = True
try:
    for name, circ in NEGATIVE.items():
        found, info = some_rotation_is_square(circ, extra=[k >= 0])
        if not found:
            print(f"{name:40s} -> UNSAT: mutant NOT caught")
            ok = False
            continue
        kv = info[2][k].as_long()
        w = word(circ, kv)
        brute_anti = run_antisq([w])[w]
        verdict = "caught, confirmed by brute force" if not brute_anti else "caught, but brute force says anti-square"
        ok &= not brute_anti
        print(f"{name:40s} -> counterexample k={kv} ({w}): {verdict}")
    for name, circ in POSITIVE.items():
        found, info = some_rotation_is_square(circ, extra=[k >= 0])
        print(f"{name:40s} -> {'UNSAT as expected' if not found else 'counterexample k=' + str(info[2][k]) + ': CONTROL FAILED'}")
        ok &= not found
except Inconclusive as e:
    print("INCONCLUSIVE:", e, file=sys.stderr)
    sys.exit(3)
print("ALL EXPECTATIONS MET" if ok else "FAILURES ABOVE")
sys.exit(0 if ok else 1)
