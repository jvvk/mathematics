"""Search for h = c0 + h0 on a reflexive polygon with CT(h^n) = λ^n f_n for n <= 8, where f is the holomorphic
solution of D, λ = ±3 and c0 = 4λ = ±12 (CT(h) = λ f_1, forced into 12Z by parity). Every nonconstant coefficient
has absolute value at most R (vertices nonzero). MAXB (default 9, i.e. all sixteen reflexive polygons) bounds the
number of boundary points; the list has GL2(Z)-duplicates, which repeat work but lose nothing. Prunes: CT(h0^2) = 2 Σ_{pairs v,-v} c_v c_-v, then CT(h0^3) via triples.

Usage: python3 search2d_chunk.py R LO HI [MAXB]   (polygon indices LO..HI-1 of the sorted list; HI = -1 for all).
Exits 1 if any model is found (the paper records none)."""
import sys
from itertools import product, combinations
from fractions import Fraction as F
from collections import defaultdict

f = [1, 4, 40, 480, 6000, 72384, 763776, 5091840, -50281920]
N = 8
R = int(sys.argv[1]) if len(sys.argv) > 1 else 4
LAMS = (3, -3)
pts = [(i, j) for i in range(-2, 3) for j in range(-2, 3)]


def hull(ps):
    ps = sorted(set(ps))
    cross = lambda o, a, b: (a[0]-o[0])*(b[1]-o[1]) - (a[1]-o[1])*(b[0]-o[0])
    lo, up = [], []
    for p in ps:
        while len(lo) >= 2 and cross(lo[-2], lo[-1], p) <= 0: lo.pop()
        lo.append(p)
    for p in reversed(ps):
        while len(up) >= 2 and cross(up[-2], up[-1], p) <= 0: up.pop()
        up.append(p)
    return lo[:-1] + up[:-1]


def inside(poly, p, strict):
    for k in range(len(poly)):
        o, a = poly[k], poly[(k+1) % len(poly)]
        c = (a[0]-o[0])*(p[1]-o[1]) - (a[1]-o[1])*(p[0]-o[0])
        if c < 0 or (strict and c == 0):
            return False
    return True


def gl2_canon(lat):
    """Canonical form under GL2(Z) acting on the (small) point set: brute force over small matrices."""
    best = None
    for a, b, c, d in product(range(-2, 3), repeat=4):
        if abs(a*d - b*c) != 1:
            continue
        q = tuple(sorted((a*x + b*y, c*x + d*y) for x, y in lat))
        if best is None or q < best:
            best = q
    return best


seen, polys = set(), []
cands = [p for p in pts if p != (0, 0)]
for k in range(3, 7):
    for vs in combinations(cands, k):
        h = hull(list(vs))
        if len(h) != k:
            continue
        if [p for p in pts if inside(h, p, True)] != [(0, 0)]:
            continue
        lat = [p for p in pts if inside(h, p, False) and p != (0, 0)]
        key = gl2_canon(lat)
        if key in seen:
            continue
        seen.add(key)
        polys.append((tuple(h), lat))
print("reflexive polygons found:", len(polys), flush=True)
import time; T0 = time.time()

hits = 0
MAXB = int(sys.argv[4]) if len(sys.argv) > 4 else 9
PL = [t for t in sorted(polys, key=lambda t: len(t[1])) if len(t[1]) <= MAXB]
LO, HI = int(sys.argv[2]), int(sys.argv[3])
HI = len(PL) if HI < 0 else HI
print("polygons with at most", MAXB, "boundary points:", len(PL), "searching", LO, "to", HI - 1, flush=True)
for verts, lat in PL[LO:HI]:
    pairs = [(i, lat.index((-p[0], -p[1]))) for i, p in enumerate(lat) if (-p[0], -p[1]) in lat and lat.index((-p[0], -p[1])) > i]
    tris = [(i, j, k) for i in range(len(lat)) for j in range(i+1, len(lat)) for k in range(j+1, len(lat))
            if all(lat[i][d] + lat[j][d] + lat[k][d] == 0 for d in (0, 1))]
    if not tris:
        continue
    ranges = [tuple(c for c in range(-R, R+1) if c != 0) if p in verts else tuple(range(-R, R+1)) for p in lat]
    print('polygon', verts, len(lat), round(time.time()-T0), flush=True)
    for lam in LAMS:
        c0 = 4 * lam
        from math import comb
        e = [sum(comb(k, j) * (-c0)**(k-j) * F(lam)**j * f[j] for j in range(k+1)) for k in range(4)]
        for cs in product(*ranges):
            if 2 * sum(cs[i] * cs[j] for i, j in pairs) != e[2]:
                continue
            if 6 * sum(cs[i] * cs[j] * cs[k] for i, j, k in tris) != e[3]:
                continue
            coef = [(p, c) for p, c in zip(lat, cs) if c]
            cur, ok = {(0, 0): 1}, True
            for n in range(1, N + 1):
                nxt = defaultdict(int)
                for (u, v), a in cur.items():
                    nxt[(u, v)] += a * c0
                    for (p, q), c in coef:
                        nxt[(u+p, v+q)] += a * c
                cur = nxt
                if cur.get((0, 0), 0) != lam**n * f[n]:
                    ok = False
                    break
            if ok:
                hits += 1
                print("HIT verts", verts, "coef", dict(coef), "c0", c0, flush=True)
print("hits:", hits, "time", round(time.time()-T0))
if hits:
    sys.exit("FAIL: a model was found, contradicting the paper")
print("PASS: no model in this range")
