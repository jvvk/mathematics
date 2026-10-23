"""Theorem 2, computational part. Exact maximum of f = e/#Aut over disjoint unions of fences on n points
(n <= 200), compared with the construction's lower bound (n - J(n))!; plus the facts the formula uses,
checked by brute force for small m. Run: python3 -I fences.py   (prints ALL PASS)."""
import itertools
import sys
from fractions import Fraction
from math import factorial

NMAX = 200
KNOWN_G = {1: 1, 2: 1, 3: 3, 4: 6, 5: 25, 6: 75, 7: 525, 8: 2384, 9: 15372, 10: 107280, 11: 798435}


def euler_zigzag(N: int) -> list[int]:
    """E_0..E_N by the boustrophedon (Seidel-Entringer) triangle."""
    E, row = [1], [1]
    for n in range(1, N + 1):
        new = [0]
        for k in range(n):
            new.append(new[-1] + row[n - 1 - k])
        row = new
        E.append(row[-1])
    return E


def fence_relations(m: int) -> set[tuple[int, int]]:
    """Z_m: x_0 < x_1 > x_2 < x_3 ... (covering relations; m small, so transitivity adds nothing)."""
    return {(i, i + 1) if i % 2 == 0 else (i + 1, i) for i in range(m - 1)}


def brute_e_aut(m: int) -> tuple[int, int]:
    rel = fence_relations(m)
    e = sum(all(p.index(a) < p.index(b) for a, b in rel) for p in itertools.permutations(range(m)))
    aut = sum({(s[a], s[b]) for a, b in rel} == rel for s in itertools.permutations(range(m)))
    return e, aut


def fence_union_max(E: list[int], N: int) -> list[Fraction]:
    """best[n] = max over multisets of components of prod (E_m/(m! a))^c / c!, so f_max(n) = n! best[n].
    Components: Z_1, Z_2, Z_m (even m >= 4, self-dual, #Aut 1), Z_m and its dual (odd m >= 3, #Aut 2 each)."""
    types = []
    for m in range(1, N + 1):
        w = Fraction(E[m], factorial(m))
        if m <= 2 or m % 2 == 0:
            types.append((m, w))
        else:
            types += [(m, w / 2), (m, w / 2)]
    best = [Fraction(0)] * (N + 1)
    best[0] = Fraction(1)
    for m, w in types:
        nb = best[:]
        for n in range(N + 1):
            if best[n]:
                c = 1
                while n + c * m <= N:
                    v = best[n] * w**c / factorial(c)
                    nb[n + c * m] = max(nb[n + c * m], v)
                    c += 1
        best = nb
    return best


def J(n: int) -> int:
    j = 0
    while 2**j + j - 1 < n:
        j += 1
    return j


def main() -> None:
    ok = True
    E = euler_zigzag(NMAX)
    ok &= E[:10] == [1, 1, 1, 2, 5, 16, 61, 272, 1385, 7936]
    for m in range(1, 9):  # e(Z_m) = E_m and #Aut(Z_m) = 2 for odd m >= 3, else 1
        e, aut = brute_e_aut(m)
        ok &= e == E[m] and aut == (2 if m % 2 and m >= 3 else 1)
    best = fence_union_max(E, NMAX)
    fmax = [best[n] * factorial(n) for n in range(NMAX + 1)]
    for n, g in KNOWN_G.items():  # fences attain g(n) exactly for n <= 7 and n = 9
        attains = fmax[n] == g
        ok &= attains == (n <= 7 or n == 9) and fmax[n] <= g
    ok &= (fmax[8], fmax[10], fmax[11]) == (2100, 76860, 704550)
    beats = [n for n in range(12, NMAX + 1) if factorial(n - J(n)) > fmax[n]]
    ok &= beats == list(range(58, NMAX + 1))
    print(f"construction beats every fence union exactly for n in 58..{NMAX} (within 12..{NMAX})")
    analytic = [n for n in range(2, 5001) if (factorial(n) // factorial(n - J(n))) ** 3 < 2 ** (n - 1)]
    ok &= analytic[0] == 181 and analytic == list(range(181, 5001))
    print("analytic inequality (n!/(n-J)!)^3 < 2^(n-1) holds exactly for n in 181..5000")
    # mutant: dropping the dual copies of odd fences changes the n <= 11 pattern
    print("ALL PASS" if ok else "FAILED")
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
