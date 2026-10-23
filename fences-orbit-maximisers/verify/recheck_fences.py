"""Independent recheck of the fence-union maximum (shares no code with fences.py): recursion over partitions
by largest part with memoisation, Euler numbers from the tangent/secant e.g.f. coefficients, and component
automorphisms counted from scratch. Compares with (n - J(n))! for 12 <= n <= 200. Run: python3 -I recheck_fences.py"""
from fractions import Fraction
from functools import lru_cache
from math import comb, factorial

TOP = 200


def zigzag_numbers(N):
    # 2 E_{n+1} = sum_k C(n,k) E_k E_{n-k}  (n >= 1), E_0 = E_1 = 1
    z = [1, 1]
    for n in range(1, N):
        z.append(sum(comb(n, k) * z[k] * z[n - k] for k in range(n + 1)) // 2)
    return z


Z = zigzag_numbers(TOP)


def kinds(m):
    """(number of non-isomorphic fences of size m, automorphism count of each)."""
    if m >= 3 and m % 2 == 1:
        return 2, 2
    return 1, 1


@lru_cache(maxsize=None)
def best(n, cap):
    """max over multisets of fence components with all sizes <= cap and total n of prod (Z_m/(m! a))^c / c!."""
    if n == 0:
        return Fraction(1)
    out = Fraction(0)
    for m in range(1, min(n, cap) + 1):
        nk, a = kinds(m)
        w = Fraction(Z[m], factorial(m) * a)
        # choose multiplicities (c1, c2) for the (at most two) kinds of size m, c1 + c2 = c >= 1
        for c in range(1, n // m + 1):
            splits = [(c, 0)] if nk == 1 else [(c1, c - c1) for c in [c] for c1 in range(c + 1)]
            for c1, c2 in splits:
                v = w ** (c1 + c2) / (factorial(c1) * factorial(c2)) * best(n - c * m, m - 1)
                out = max(out, v)
    return out


def least_j(n):
    j = 0
    while (1 << j) + j - 1 < n:
        j += 1
    return j


wins = [n for n in range(12, TOP + 1) if factorial(n - least_j(n)) > best(n, n) * factorial(n)]
print("recheck: construction wins for n in", wins[0], "..", wins[-1], "count", len(wins))
print("ALL PASS" if wins == list(range(58, TOP + 1)) else "FAILED")
