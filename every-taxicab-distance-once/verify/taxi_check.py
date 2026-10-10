"""Verify chapter 11 (MSE q/4967838): n lattice points with taxicab distances exactly 1, ..., N = C(n,2).

  1. The parity condition: with a + b = n points of the two colours (parity of x+y), a*b = ceil(N/2) has an integer
     solution iff n is a square (n = 0,1 mod 4) or n - 2 is a square (n = 2,3 mod 4); checked for n <= 400.
  2. The explicit placements for n = 2, 3, 4, 6, 9, 11 have distances exactly 1..N, with the predicted colour split.
MUTANT=1 uses floor(N/2); MUTANT=2 moves one point of the n = 11 placement. Each must FAIL.
"""
from __future__ import annotations

import math
import os
import sys
from itertools import combinations

MUTANT = int(os.environ.get("MUTANT", "0"))
SOL = {
    2: [(0, 0), (0, 1)],
    3: [(0, 0), (0, 2), (0, 3)],
    4: [(0, 0), (0, 2), (0, 5), (0, 6)],
    6: [(0, 0), (0, 14), (0, 15), (1, 4), (1, 6), (1, 12)],
    9: [(6, -3), (6, -2), (1, -9), (-6, 6), (4, -2), (0, -2), (-10, -17), (-26, 0), (-5, 2)],
    11: [(0, 14), (0, 16), (1, 16), (7, 11), (8, 7), (11, 2), (12, 7), (14, 45), (17, 49), (23, 0), (23, 26)],  # as printed in the book (A..K)
}
if MUTANT == 2:
    SOL[11][0] = (0, 15)


def is_sq(m: int) -> bool:
    return m >= 0 and math.isqrt(m) ** 2 == m


def splits(n: int) -> list[tuple[int, int]]:
    N = n * (n - 1) // 2
    odd = N // 2 if MUTANT == 1 else (N + 1) // 2
    return [(a, n - a) for a in range(n + 1) if a * (n - a) == odd]


def main() -> int:
    ok = True
    agree = all(bool(splits(n)) == (is_sq(n) if n % 4 in (0, 1) else is_sq(n - 2)) for n in range(2, 401))
    allowed = [n for n in range(2, 60) if splits(n)]
    print(f"1. parity condition matches the square rule for n <= 400: {agree}; allowed n < 60: {allowed}")
    ok &= agree
    for n, P in SOL.items():
        N = n * (n - 1) // 2
        d = sorted(abs(a - c) + abs(b - e) for (a, b), (c, e) in combinations(P, 2))
        col = sum((x + y) % 2 for x, y in P)
        good = d == list(range(1, N + 1)) and (col, n - col) in splits(n) + [(b, a) for a, b in splits(n)]
        print(f"2. n={n:2d}: distances 1..{N} exactly once: {d == list(range(1, N + 1))}; colour split {col}/{n - col}: {good}")
        ok &= good
    print("PASS" if ok else "FAIL")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
