"""Search 2-variable Laurent f on the square [-1,1]^2 with CT(f^n) = binom(2n,n), n <= 8,
origin interior, and report edge discriminants (squarefree edges wanted) and CT(f^(p-1)) mod p."""
import itertools
from math import comb
from collections import defaultdict

PTS = [(i, j) for i in (-1, 0, 1) for j in (-1, 0, 1)]
COEF = (-2, -1, 0, 1, 2)
TARGET = [comb(2 * n, n) for n in range(9)]


def cross(o, a, b):
    return (a[0]-o[0])*(b[1]-o[1]) - (a[1]-o[1])*(b[0]-o[0])


def hull(points):
    pts = sorted(set(points))
    lo, up = [], []
    for p in pts:
        while len(lo) >= 2 and cross(lo[-2], lo[-1], p) <= 0: lo.pop()
        lo.append(p)
    for p in reversed(pts):
        while len(up) >= 2 and cross(up[-2], up[-1], p) <= 0: up.pop()
        up.append(p)
    return lo[:-1] + up[:-1]


def origin_interior(points):
    V = hull(points)
    return len(V) >= 3 and all(cross(a, b, (0, 0)) > 0 for a, b in zip(V, V[1:] + V[:1]))


def mul(f: dict, g: dict) -> dict:
    out: dict = defaultdict(int)
    for u, a in f.items():
        for v, b in g.items():
            out[(u[0] + v[0], u[1] + v[1])] += a * b
    return {k: c for k, c in out.items() if c}


def ct_powers(f: dict, N: int) -> list[int]:
    res, g = [1], {(0, 0): 1}
    for n in range(1, N + 1):
        g = mul(g, f)
        c = g.get((0, 0), 0)
        if c != TARGET[n]:
            return res + [c]
        res.append(c)
    return res


if __name__ == "__main__":
    hits = []
    nonzero = [p for p in PTS if p != (0, 0)]
    for cs in itertools.product(COEF, repeat=8):
        f = {p: c for p, c in zip(nonzero, cs) if c}
        if not f:
            continue
        if not origin_interior(f):
            continue  # origin must be interior
        for c0 in COEF:
            ff = dict(f)
            if c0:
                ff[(0, 0)] = c0
            if ct_powers(ff, 8) == TARGET:
                hits.append(ff)
    print("hits:", len(hits))
    for ff in hits[:10]:
        print(sorted(ff.items()))
