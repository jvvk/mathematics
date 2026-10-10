"""Independent recheck (shares no code with ../): a_n by exact polynomials for n <= 18, and the census of classes and
unexplained classes for n <= 16 with its own move search (every cut mask) and exact rational linear algebra at four
rational points instead of arithmetic modulo a prime.

    timeout 3600 nice -n 15 python3 recheck.py        -> prints R1, R2 and ALL AGREE / DISAGREE
    python3 recheck.py --mutant                        -> drops the boundary conditions; R2 must then disagree
"""

import sys
from fractions import Fraction as F
from itertools import product

MUTANT = "--mutant" in sys.argv
A_NOTE = [
    2,
    3,
    6,
    10,
    20,
    36,
    72,
    134,
    270,
    526,
    1052,
    2072,
    4154,
    8231,
    16504,
    32856,
    65764,
    131249,
]
TABLE = {8: (2, 0), 9: (2, 2), 10: (2, 0), 11: (4, 0), 12: (8, 0), 13: (6, 2), 14: (25, 0), 15: (8, 0),
         16: (40, 0)}
TS = [F(5, 2), F(-7, 3), F(11, 4), F(13, 5)]


def poly(w):
    """det(tI - H_w) coefficients, via P_k = (t - w_k) P_{k-1} - P_{k-2} written on coefficient lists."""
    prev, cur = [0], [1]
    for ch in w:
        nxt = [0] + cur
        for i, c in enumerate(cur):
            nxt[i] -= int(ch) * c
        for i, c in enumerate(prev):
            nxt[i] -= c
        prev, cur = cur, nxt
    return tuple(cur)


def a_count(n):
    return len({poly("".join(b)) for b in product("01", repeat=n)})


def mat(w, t):
    """Transfer matrix [[a, b], [c, d]] of w at the rational t."""
    a, b, c, d = F(1), F(0), F(0), F(1)
    for ch in w:
        z = t - int(ch)
        a, b, c, d = a * z + b, -a, c * z + d, -c
    return a, b, c, d


def nullspace(rows):
    rows = [list(r) for r in rows]
    piv = []
    r = 0
    for col in range(3):
        k = next((i for i in range(r, len(rows)) if rows[i][col] != 0), None)
        if k is None:
            continue
        rows[r], rows[k] = rows[k], rows[r]
        rows[r] = [x / rows[r][col] for x in rows[r]]
        for i in range(len(rows)):
            if i != r and rows[i][col] != 0:
                f = rows[i][col]
                rows[i] = [x - f * y for x, y in zip(rows[i], rows[r])]
        piv.append(col)
        r += 1
    out = []
    for fc in [c for c in range(3) if c not in piv]:
        v = [F(0)] * 3
        v[fc] = F(1)
        for i, c in enumerate(piv):
            v[c] = -rows[i][fc]
        out.append(v)
    return out


def g_exists(A, blocks, B, A2, B2, t):
    rows = []
    for Y in set(blocks):
        a, b, c, d = mat(Y, t)
        rows.append((c, d - a, -b))  # (M G)_{10} = (M G)_{01}

    def par(x, y):
        return (x[0] * y[1], x[1] * y[1] - x[0] * y[0], -x[1] * y[0])

    mA, mB, mA2, mB2 = mat(A, t), mat(B, t), mat(A2, t), mat(B2, t)
    xA, xA2 = (mA[0], mA[1]), (mA2[0], mA2[1])
    yB, yB2 = (mB[0], mB[2]), (mB2[0], mB2[2])
    if not MUTANT:
        rows += [par(xA, yB2), par(xA2, yB)]
    K = nullspace(rows)
    cands = K + ([[sum(c) for c in zip(*K)]] if len(K) > 1 else [])
    for al, be, ga in cands:
        if al * ga - be * be == 0 and not MUTANT: continue
        Gx = (al * xA[0] + be * xA[1], be * xA[0] + ga * xA[1])
        Gx2 = (al * xA2[0] + be * xA2[1], be * xA2[0] + ga * xA2[1])
        i = 0 if yB2[0] != 0 else 1; j = 0 if yB[0] != 0 else 1
        if MUTANT or Gx[i] * yB[j] == Gx2[j] * yB2[i]:   # lam = lam'
            return True
    return False


def move_exists(u, v):
    n = len(u)
    for vv in {v, v[::-1]}:
        for a in range(n - 1):
            for b in range(n - a - 1):
                L = n - a - b
                X = u[a : a + L]
                for mask in range(1, 2 ** (L - 1)):
                    cuts = [0] + [i + 1 for i in range(L - 1) if mask >> i & 1] + [L]
                    blocks = [X[cuts[i] : cuts[i + 1]] for i in range(len(cuts) - 1)]
                    rev = "".join(blocks[::-1])
                    for la in range(n - L + 1):
                        if vv[la : la + L] != rev:
                            continue
                        A2, B2 = vv[:la], vv[la + L :]
                        if all(
                            g_exists(u[:a], blocks, u[n - b :], A2, B2, t) for t in TS
                        ):
                            return True
    return False


def census(n):
    groups = {}
    for bits in product("01", repeat=n):
        w = "".join(bits)
        if w <= w[::-1]:
            groups.setdefault(poly(w), []).append(w)
    comp = lambda w: w.translate(str.maketrans("01", "10"))
    cls = [g for g in groups.values() if len(g) > 1]
    unexpl = 0
    for g in cls:
        parent = list(range(len(g)))

        def root(i):
            while parent[i] != i:
                i = parent[i]
            return i

        for i in range(len(g)):
            for j in range(i + 1, len(g)):
                u, v = g[i], g[j]
                if v in (comp(u), comp(u)[::-1]) or move_exists(u, v):
                    parent[root(i)] = root(j)
        unexpl += len({root(i) for i in range(len(g))}) > 1
    return len(cls), unexpl


if __name__ == "__main__":
    ok = True
    if not MUTANT:
        a = [a_count(n) for n in range(1, 19)]
        print(
            "R1 a_n for n <= 18:",
            "agree" if a == A_NOTE else f"DISAGREE {a}",
            flush=True,
        )
        ok &= a == A_NOTE
    tab = {n: census(n) for n in TABLE}
    print("R2 census n <= 16:", tab, flush=True)
    ok &= tab == TABLE
    print("ALL AGREE" if ok else "DISAGREE")
    sys.exit(0 if ok else 1)
