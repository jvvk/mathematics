"""Shape A of Friedman's unsolved problem 15 cannot be arranged in any square: a solver-free check.

Shape A (unsolved list, May 2007 heptominoes, leftmost):   .##
                                                            .#.
                                                            .#.
                                                            .#.
                                                            ##.
Its row counts are P = (2,1,1,1,2) and column counts Q = (1,5,1) (both palindromes), so every rotation
or reflection has profiles P and Q, possibly exchanged.

Weight argument. Give cell (x, y) of the n x n square the weight w[x] + w[y]. A copy of A then weighs
P.w[i..i+4] + Q.w[j..j+2] for some i, j. If every P-window is >= p and every Q-window is >= q with
p + q >= 0, every copy, and hence every union of copies, has weight >= 0. An arrangement with c cells in
every row and column weighs 2c * sum(w). So sum(w) < 0 rules the square out.

Family for n = 5K + m (K >= 1, m = 5..9), with p = -1 and q = 1:
    w = [a_K Z + d, ..., a_2 Z + d, a_1 Z + d, C_m],   Z = (-5,1,0,-1,5), d = (-1/2,1/2,0,1/2,-1/2),
    a_1 = 7/2, a_{k+1} = 5 a_k, and C_m a fixed core (shapeA_family.json).
Every block sums to 0, so sum(w) = sum(C_m) < 0. Windows inside a block do not depend on its scale.
A window across the boundary of blocks with scales 5s and s has value A s + D with A > 0 (checked
below), so it holds for every s >= a_1 once it holds at s = a_1. Windows at the core are fixed. The
leftmost block has fewer windows (nothing lies beyond the edge). Sides 5..9 use separate exact
certificates; smaller sides cannot hold the shape.
Usage: python3 check_shapeA.py [NMAX]
"""

from __future__ import annotations

import json
import sys
from fractions import Fraction as F
from pathlib import Path

HERE = Path(__file__).resolve().parent
SHAPE = [".##", ".#.", ".#.", ".#.", "##."]


def profiles(rows: list[str]) -> tuple[list[int], list[int]]:
    return [r.count("#") for r in rows], [
        sum(r[i] == "#" for r in rows) for i in range(len(rows[0]))
    ]


def windows_ok(w: list[F], P: list[int], Q: list[int]) -> tuple[bool, F]:
    n = len(w)
    if n < max(len(P), len(Q)):
        return False, F(0)
    p = min(sum(P[j] * w[i + j] for j in range(len(P))) for i in range(n - len(P) + 1))
    q = min(sum(Q[j] * w[i + j] for j in range(len(Q))) for i in range(n - len(Q) + 1))
    return p + q >= 0 and sum(w) < 0, p + q


def family(fam: dict, n: int) -> list[F]:
    K, m = divmod(n - 5, 5)
    m += 5  # n = 5K + m with m in 5..9 and K >= 1 when n >= 10
    Z, d, a1 = fam["Z"], [F(x) for x in fam["d"]], F(fam["a1"])
    blocks = []
    for k in range(K, 0, -1):
        a = a1 * F(fam["ratio"]) ** (k - 1)
        blocks += [a * z + dd for z, dd in zip(Z, d)]
    return blocks + [F(x) for x in fam["cores"][str(m)]]


def induction_ok(fam: dict, P: list[int], Q: list[int]) -> bool:
    """Every window crossing a block boundary is A s + D with A > 0, and holds at s = a_1."""
    Z, d, a1, r = fam["Z"], [F(x) for x in fam["d"]], F(fam["a1"]), F(fam["ratio"])

    def pair(s: F) -> list[F]:
        return [r * s * z + dd for z, dd in zip(Z, d)] + [
            s * z + dd for z, dd in zip(Z, d)
        ]

    for L, bound in ((P, F(-1)), (Q, F(1))):
        for i in range(10 - len(L) + 1):
            if i + len(L) <= 5 or i >= 5:
                continue  # inside one block: scale-free, checked by the explicit sides
            val = lambda s: sum(L[j] * pair(s)[i + j] for j in range(len(L)))
            A, D = val(F(1)) - val(F(0)), val(F(0))
            if not (A > 0 and A * a1 + D >= bound):
                return False
    return True


def main(nmax: int) -> None:
    P, Q = profiles(SHAPE)
    assert (P, Q) == ([2, 1, 1, 1, 2], [1, 5, 1]) and P == P[::-1] and Q == Q[::-1]
    fam = json.loads((HERE / "shapeA_family.json").read_text())
    assert fam["P"] == P and fam["Q"] == Q
    assert sum(F(x) for x in fam["d"]) == 0 and sum(fam["Z"]) == 0
    assert induction_ok(fam, P, Q), "induction step fails"
    small = {}
    for line in (HERE / "exact-weights-A.jsonl").read_text().splitlines():
        rec = json.loads(line)
        small[rec["side"]] = [F(x) for x in rec["weights"]]
    for n in range(5, 10):
        ok, _ = windows_ok(small[n], P, Q)
        assert ok, f"side {n}: certificate fails"
    for n in range(10, nmax + 1):
        w = family(fam, n)
        assert len(w) == n
        ok, _ = windows_ok(w, P, Q)
        assert ok, f"side {n}: family fails"
    print(
        f"shape A: certified impossible on every side 5..{nmax} explicitly, and for all n >= 10 by induction"
    )

    # mutants: each must be rejected
    bad = json.loads(json.dumps(fam))
    bad["cores"]["7"][0] = str(F(bad["cores"]["7"][0]) - 5)
    assert not windows_ok(family(bad, 12), P, Q)[0]
    bad = json.loads(json.dumps(fam))
    bad["ratio"] = 4  # below 4.8 the boundary windows fail
    assert not induction_ok(bad, P, Q)
    bad = json.loads(json.dumps(fam))
    bad["d"] = ["0"] * 5  # without the offset the in-block Q-windows are 0 < 1
    assert not windows_ok(family(bad, 23), P, Q)[0]
    Pw, Qw = [2, 1, 1, 1, 2], [1, 4, 2]  # a wrong column profile
    assert not all(windows_ok(family(fam, n), Pw, Qw)[0] for n in range(10, 40))
    print("mutants rejected: bad core, ratio 4, no offset, wrong profile")


if __name__ == "__main__":
    main(int(sys.argv[1]) if len(sys.argv) > 1 else 400)
