"""Shuffle-square test for binary words as integer feasibility, and a parametric proof for the family
W_k = 0^{k+5} 1 0^2 1^4 0^{k+4} 1^3 0 1^4  (length 24 + 2k, twelve 1s).

A linear binary word with m ones is 0^{e_0} 1 0^{e_1} 1 ... 1 0^{e_m}. It is a shuffle square iff the ones split
into sets A, B of size m/2 and each gap e_i splits as x_i + y_i (x_i to copy A) so that the two copies have equal
zero-runs: for j = 0..m/2, zeros of A between its j-th and (j+1)-th one = zeros of B between its j-th and (j+1)-th.
(Zeros inside one gap are interchangeable, so any split is realisable; this condition is exact.)
A rotation cuts the circular word inside the gap c_t before the t-th one at offset s in [0, c_t].
"""

from __future__ import annotations

import itertools
import random
import subprocess
import sys

from z3 import And, Int, Solver, Sum, sat


def copy_zero_runs(ones: tuple[int, ...], z: list, m: int) -> list:
    """Zero-run lengths of the copy owning the 1s at indices `ones` (1..m); z[i] = its share of gap i (0..m)."""
    bounds = [0] + list(ones) + [m + 1]
    return [
        Sum([z[i] for i in range(bounds[j], bounds[j + 1])])
        for j in range(len(bounds) - 1)
    ]


def rotation_constraints(circ: list, t: int, s, x: list, A: tuple[int, ...]) -> list:
    """circ: circular gaps (z3 terms or ints), gap circ[j] precedes one j (0-indexed); cut inside gap t at offset s."""
    m = len(circ)
    e = (
        [s] + [circ[(t + i) % m] for i in range(1, m)] + [circ[t] - s]
    )  # linear gaps e_0..e_m
    B = tuple(i for i in range(1, m + 1) if i not in A)
    y = [e[i] - x[i] for i in range(m + 1)]
    cons = [And(x[i] >= 0, x[i] <= e[i]) for i in range(m + 1)] + [s >= 0, s <= circ[t]]
    ra, rb = copy_zero_runs(A, x, m), copy_zero_runs(B, y, m)
    return cons + [ra[j] == rb[j] for j in range(len(ra))]


def partitions(m: int):
    # WLOG the first one belongs to A (swap the copies otherwise).
    for rest in itertools.combinations(range(2, m + 1), m // 2 - 1):
        yield (1,) + rest


def some_rotation_is_square(circ: list, extra: list = ()) -> tuple[bool, object]:
    m = len(circ)
    for t in range(m):
        for A in partitions(m):
            sv = Solver()
            s = Int("s")
            x = [Int(f"x{i}") for i in range(m + 1)]
            sv.add(*extra, *rotation_constraints(circ, t, s, x, A))
            if sv.check() == sat:
                return True, (t, A, sv.model())
    return False, None


def circ_gaps(w: str) -> list[int]:
    """Circular gaps of a binary word with at least one 1: gap j = zeros before the j-th 1 (cyclically)."""
    ones = [i for i, c in enumerate(w) if c == "1"]
    n = len(w)
    return [
        (ones[j] - ones[j - 1] - 1) % n if j else (ones[0] + n - ones[-1] - 1)
        for j in range(len(ones))
    ]


def validate(trials: int) -> None:
    rng = random.Random(7)
    words = []
    while len(words) < trials:
        n = rng.choice([8, 10, 12, 14, 16, 18])
        w = "".join(rng.choice("01") for _ in range(n))
        if w.count("1") % 2 == 0 and w.count("0") % 2 == 0 and 0 < w.count("1") <= 8:
            words.append(w)
    words += ["000001001111000011101111"]  # the length-24 anti-square
    out = subprocess.run(
        ["./antisq"], input="\n".join(words) + "\n", capture_output=True, text=True
    ).stdout.split()
    brute = dict(zip(out[1::2], (v == "1" for v in out[0::2])))
    bad = 0
    for w in words:
        anti_ilp = not some_rotation_is_square(circ_gaps(w))[0]
        if anti_ilp != brute[w]:
            bad += 1
            print("MISMATCH", w, anti_ilp, brute[w])
    print(
        f"validated {len(words)} words, mismatches {bad}, anti-squares among them {sum(brute.values())}"
    )


def family_proof() -> None:
    k = Int("k")
    a, b = k + 5, k + 4
    circ = [a, 2, 0, 0, 0, b, 0, 0, 1, 0, 0, 0]  # gap before each of the 12 ones
    found, info = some_rotation_is_square(circ, extra=[k >= 0])
    if found:
        t, A, mdl = info
        print("COUNTEREXAMPLE: k =", mdl[k], "cut gap", t, "A =", A)
    else:
        print(
            "PROVED: for every integer k >= 0, no rotation of W_k is a shuffle square (all 12 x 462 systems UNSAT)."
        )


if __name__ == "__main__":
    if sys.argv[1] == "validate":
        validate(int(sys.argv[2]))
    else:
        family_proof()
