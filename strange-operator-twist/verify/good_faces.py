"""Among 2-variable f with CT(f^n)=binom(2n,n), keep those whose own faces pass BV's k=1 face test
(vertex coeffs = +-2^a, length-2 edges with discriminant b^2-4ac = +-2^a), then compute the
k=1 Hasse-Witt entry of the product face Delta_f x {v}: c^(p-1) CT(f^(p-1))."""
import itertools
from math import comb
from search_f import mul, ct_powers, PTS, COEF

def hull(points):
    pts = sorted(set(points))
    def cross(o, a, b): return (a[0]-o[0])*(b[1]-o[1]) - (a[1]-o[1])*(b[0]-o[0])
    lo, up = [], []
    for p in pts:
        while len(lo) >= 2 and cross(lo[-2], lo[-1], p) <= 0: lo.pop()
        lo.append(p)
    for p in reversed(pts):
        while len(up) >= 2 and cross(up[-2], up[-1], p) <= 0: up.pop()
        up.append(p)
    return lo[:-1] + up[:-1]

def pow2(n: int) -> bool:
    n = abs(n)
    return n > 0 and n & (n - 1) == 0

def good(f: dict) -> bool:
    V = hull(list(f))
    if not all(pow2(f[v]) for v in V):
        return False
    for a, b in zip(V, V[1:] + V[:1]):
        mid = ((a[0]+b[0])//2, (a[1]+b[1])//2)
        if (a[0]+b[0]) % 2 == 0 and (a[1]+b[1]) % 2 == 0:  # length-2 edge
            disc = f.get(mid, 0)**2 - 4*f[a]*f[b]
            if not pow2(disc):
                return False
    return True

nonzero = [p for p in PTS if p != (0, 0)]
found = []
for cs in itertools.product(COEF, repeat=8):
    f = {p: c for p, c in zip(nonzero, cs) if c}
    if not f: continue
    xs = [p[0] for p in f]; ys = [p[1] for p in f]
    if not (min(xs) < 0 < max(xs) and min(ys) < 0 < max(ys)): continue
    for c0 in COEF:
        ff = dict(f)
        if c0: ff[(0, 0)] = c0
        if len(ct_powers(ff, 8)) == 9 and good(ff):
            found.append(ff)
print("binom(2n,n) models with good own faces:", len(found))
for ff in found[:5]:
    print(sorted(ff.items()), "vertices", hull(list(ff)))
# product-face entry: independent of f, equals CT(f^(p-1)) = binom(2p-2,p-1) up to a unit
for ff in found[:3]:
    for p in (5, 7, 11, 13):
        g = {(0, 0): 1}
        for _ in range(p - 1): g = mul(g, ff)
        c = g.get((0, 0), 0)
        print(p, c, c % p, c == comb(2*p-2, p-1))
