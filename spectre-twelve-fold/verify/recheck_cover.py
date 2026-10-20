"""Independent recheck of the 12-fold cover for the straight-edged Spectre Tile(1,1).

Shares no code with verify.py. It works in floating point in the plane: the tile is the 14-gon with unit
edges in directions d_i * 30 degrees, each placement (r, x, y) is the tile rotated by r * 30 degrees and
translated by x a + y b, and the periodic copies are added for every lattice vector m v + n w that can reach
the sample point. At random points of one period cell it counts the tiles containing the point by the
even-odd rule and checks that the count is 12. Points within 1e-9 of a tile edge are skipped (a null set).

    python3 recheck_cover.py            # 20000 random points, about a minute
    MUTANT=1 python3 recheck_cover.py   # drops one placement; must end in FAIL
"""
import cmath
import json
import math
import os
import random
import sys
from pathlib import Path

Z = cmath.exp(1j * math.pi / 6)
D = [0, 10, 1, 3, 0, 2, 5, 7, 4, 6, 6, 8, 11, 9]
A = Z**2 + Z**3
B = -2 - Z - Z**3
V = 3 + Z + 2 * Z**2 + 3 * Z**3
W = -4 - 3 * Z + 3 * Z**2 + Z**3

verts = [0j]
for d in D:
    verts.append(verts[-1] + Z**d)
assert abs(verts[-1]) < 1e-12, "the 14-gon closes"
verts = verts[:-1]

area = 0.5 * sum((p.conjugate() * q).imag for p, q in zip(verts, verts[1:] + verts[:1]))
assert abs(area - (3 + 3 * math.sqrt(3))) < 1e-9, area
covol = (V.conjugate() * W).imag
assert abs(covol - 13.5 * (1 + math.sqrt(3))) < 1e-9, covol

placements = [tuple(p[:3]) for p in json.loads((Path(__file__).resolve().parent / "certificate.json").read_text())["placements"]]
assert len(placements) == 54 and len(set(placements)) == 54
if os.environ.get("MUTANT") == "1":
    placements = placements[1:]
assert abs(len(placements) * area / covol - 12) < 1e-9 or os.environ.get("MUTANT") == "1"

tiles = [[Z**r * p + x * A + y * B for p in verts] for r, x, y in placements]
radius = max(abs(p) for p in verts) + 1e-6


def coords(z: complex) -> tuple[float, float]:
    """Coordinates (s, t) of z in the basis v, w."""
    det = covol
    s = (z.conjugate() * W).imag / det
    t = (V.conjugate() * z).imag / det
    return s, t


def inside(z: complex, poly: list[complex]) -> int:
    """Even-odd rule; -1 when z is within 1e-9 of an edge."""
    c = False
    for p, q in zip(poly, poly[1:] + poly[:1]):
        e = q - p
        u = z - p
        lam = (u.real * e.real + u.imag * e.imag) / abs(e) ** 2
        if 0 <= lam <= 1 and abs(u - lam * e) < 1e-9:
            return -1
        if (p.imag > z.imag) != (q.imag > z.imag):
            xcross = p.real + (z.imag - p.imag) * (q.real - p.real) / (q.imag - p.imag)
            if z.real < xcross:
                c = not c
    return int(c)


def count(z: complex) -> int:
    total = 0
    for poly in tiles:
        c0 = poly[0]
        # lattice translates of this tile that can contain z
        s, t = coords(z - c0)
        span = int(math.ceil(2 * radius / min(abs(V), abs(W)))) + 3
        for m in range(math.floor(s) - span, math.floor(s) + span + 1):
            for n in range(math.floor(t) - span, math.floor(t) + span + 1):
                shift = m * V + n * W
                if abs(z - shift - c0) > 2 * radius:
                    continue
                k = inside(z - shift, poly)
                if k < 0:
                    return -1
                total += k
    return total


random.seed(516016)
N = int(os.environ.get("POINTS", "20000"))
counts: dict[int, int] = {}
for _ in range(N):
    z = random.random() * V + random.random() * W
    k = count(z)
    if k >= 0:
        counts[k] = counts.get(k, 0) + 1
print("tile area 3 + 3 sqrt3, cell area (27/2)(1 + sqrt3), 54 placements: 54 * area / cell =", round(54 * area / covol, 12))
print("coverage counts at random points:", dict(sorted(counts.items())))
ok = set(counts) == {12}
print("ALL PASS" if ok else "FAIL")
sys.exit(0 if ok else 1)
