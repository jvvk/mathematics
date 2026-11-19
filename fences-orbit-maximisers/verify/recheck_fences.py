"""Independent recheck of the fence-union maximum (shares no code with fences.py): recursion over partitions
by largest part with memoisation, Euler numbers from the tangent/secant e.g.f. coefficients, and component
automorphisms counted from scratch. Compares with (n - J(n))! for 12 <= n <= 200, and Q + U, R + U with the fence maximum for 8 <= n <= 57. Run: python3 -I recheck_fences.py"""
import sys
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


def down_set_count(n, below):
    """e(P) by dynamic programming over down-sets (bitmasks); below[v] = mask of elements < v."""
    ways = {0: 1}
    for size in range(n):
        nxt = {}
        for mask, w in ways.items():
            for v in range(n):
                if not mask >> v & 1 and below[v] & ~mask == 0:
                    nxt[mask | 1 << v] = nxt.get(mask | 1 << v, 0) + w
        ways = nxt
    return ways[(1 << n) - 1]


def strict_below(n, pairs):
    below = [0] * n
    for _ in range(n):
        for lo, hi in pairs:
            below[hi] |= 1 << lo | below[lo]
    return below


def automorphisms(n, below):
    """count bijections preserving the strict order, by extending partial maps element by element"""
    rel = [[bool(below[j] >> i & 1) for j in range(n)] for i in range(n)]
    def extend(img):
        k = len(img)
        if k == n:
            return 1
        total = 0
        for t in range(n):
            if t in img:
                continue
            if all(rel[i][k] == rel[img[i]][t] and rel[k][i] == rel[t][img[i]] for i in range(k)):
                total += extend(img + [t])
        return total
    return extend([])


# Q: 0<1>2<3>4<5 with 6<3; R: Q with 2<7 (independent transcription of Figure 1)
q_pairs = [(0, 1), (2, 1), (2, 3), (4, 3), (4, 5), (6, 3)]
r_pairs = q_pairs + [(2, 7)]
bq, br = strict_below(7, q_pairs), strict_below(8, r_pairs)
eq_, aq = down_set_count(7, bq), automorphisms(7, bq)
er, ar = down_set_count(8, br), automorphisms(8, br)
F = [best(n, n) * factorial(n) for n in range(TOP + 1)]
small = [n for n in range(8, 58)
         if max(comb(n, 7) * Fraction(eq_, aq) * F[n - 7], comb(n, 8) * Fraction(er, ar) * F[n - 8]) > F[n]]
print("recheck: e(Q), #Aut(Q), e(R), #Aut(R) =", eq_, aq, er, ar)
print("recheck: Q+U or R+U beats every fence union for n in", small)
wins = [n for n in range(12, TOP + 1) if factorial(n - least_j(n)) > F[n]]
print("recheck: construction wins for n in", wins[0], "..", wins[-1], "count", len(wins))
ok = (wins == list(range(58, TOP + 1)) and (eq_, aq, er, ar) == (298, 1, 1613, 1)
      and small == [8, 10, 11, 12] + list(range(14, 58)))
print("ALL PASS" if ok else "FAILED")
sys.exit(0 if ok else 1)
