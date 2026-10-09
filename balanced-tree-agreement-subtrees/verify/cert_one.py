"""Certificate for Lemma 5.1 (a = 2/5, c = 33/400) in a form Lean checks by evaluation.

Boxes in (x1, x2, x3) are integer boxes of the grid 1/N, N = 2^16, starting from [0, N]^3 and
bisected along the longest side (lowest index on ties). x4 = 1 - x1 - x2 - x3 is bounded below on a
box by l4 = max(0, N - u1 - u2 - u3). A box is DISCARDED if l1 + l2 + l3 > N (it misses the simplex)
and ACCEPTED with term j if a lower bound for term j of Phi on the box is provably >= 1. The sums
x3 + x4 = 1 - x1 - x2 and x2 + x4 = 1 - x1 - x3 are bounded below by N - u1 - u2 and N - u1 - u3:
  (S/N)^(2/5) >= r / 2^K  is certified by  r^5 N^2 <= S^2 2^(5K)  (integers),
  2^c >= Q2 / 2^KQ  by  Q2^400 <= 2^(33 + 400 KQ),   4^c >= Q4 / 2^KQ  by  Q4^200 <= 2^(33 + 200 KQ),
and the term needs 2^(K+KQ) <= Q * (r1 + r2) (pair terms) or 2^(K+KQ) <= Q2 * r (single terms).
Output: a Lean term of the bisection tree. The search is here; Lean only checks.
"""
from __future__ import annotations

import sys
from fractions import Fraction

N, K, KQ = 1 << 16, 24, 24


def iroot5(x: int) -> int:
    """floor(x ** (1/5)) for an integer x >= 0."""
    lo, hi = 0, 1 << (x.bit_length() // 5 + 2)
    while lo < hi:
        mid = (lo + hi + 1) // 2
        if mid**5 <= x:
            lo = mid
        else:
            hi = mid - 1
    return lo


def iroot(x: int, n: int) -> int:
    lo, hi = 0, 1 << (x.bit_length() // n + 2)
    while lo < hi:
        mid = (lo + hi + 1) // 2
        if mid**n <= x:
            lo = mid
        else:
            hi = mid - 1
    return lo


Q2 = iroot(2 ** (33 + 400 * KQ), 400)  # floor(2^(33/400) * 2^KQ)
Q4 = iroot(2 ** (33 + 200 * KQ), 200)  # floor(2^(33/200) * 2^KQ)
assert Q2**400 <= 2 ** (33 + 400 * KQ) and Q4**200 <= 2 ** (33 + 200 * KQ)


def rlow(S: int) -> int:
    """Largest r with r^5 N^2 <= S^2 2^(5K): r / 2^K <= (S/N)^(2/5)."""
    return iroot5((S * S << (5 * K)) // (N * N))


def try_accept(l1: int, l2: int, l3: int, l4: int, u1: int, u2: int, u3: int):
    pairs = [(0, l1, l4), (1, l2, l3)]
    # x3 + x4 = 1 - x1 - x2 and x2 + x4 = 1 - x1 - x3
    singles = [(2, l1 + l2), (3, N - min(N, u1 + u2)), (4, l1 + l3), (5, N - min(N, u1 + u3))]
    for j, S in singles:
        r = rlow(S)
        if Q2 * r >= 1 << (K + KQ):
            return (j, r, 0)
    for j, S1, S2 in pairs:
        r1, r2 = rlow(S1), rlow(S2)
        if Q4 * (r1 + r2) >= 1 << (K + KQ):
            return (j, r1, r2)
    return None


stats = {"accept": 0, "discard": 0, "depth": 0}


def build(l: list[int], u: list[int], depth: int) -> str:
    stats["depth"] = max(stats["depth"], depth)
    if l[0] + l[1] + l[2] > N:
        stats["discard"] += 1
        return "BT.d"
    l4 = max(0, N - u[0] - u[1] - u[2])
    acc = try_accept(l[0], l[1], l[2], l4, u[0], u[1], u[2])
    if acc is not None:
        stats["accept"] += 1
        j, r1, r2 = acc
        return f"(BT.a {j} {r1} {r2})"
    w = [u[i] - l[i] for i in range(3)]
    ax = max(range(3), key=lambda i: (w[i], -i))
    if w[ax] < 2:
        sys.exit(f"cannot certify box l={l} u={u}")
    mid = (l[ax] + u[ax]) // 2
    ulo, lhi = u.copy(), l.copy()
    ulo[ax], lhi[ax] = mid, mid
    return f"(BT.s {build(l, ulo, depth + 1)} {build(lhi, u, depth + 1)})"


if __name__ == "__main__":
    term = build([0, 0, 0], [N, N, N], 0)
    print(stats, "Q2 =", Q2, "Q4 =", Q4, "chars:", len(term))
    print("2^c lower bound:", float(Fraction(Q2, 2**KQ)), " 4^c lower bound:", float(Fraction(Q4, 2**KQ)))
    with open("cert_one.lean.txt", "w") as fh:
        fh.write(f"def certN : ℕ := {N}\ndef certK : ℕ := {K}\ndef certKQ : ℕ := {KQ}\n")
        fh.write(f"def certQ2 : ℕ := {Q2}\ndef certQ4 : ℕ := {Q4}\n")
        fh.write(f"def certTree : BT :=\n  {term}\n")
