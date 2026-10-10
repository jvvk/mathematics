"""Verify chapter 12 (MSE q/1381502, original q/1378338).

  1. Lemma: r1, r2 in [1, sqrt3], angle <= 30 degrees  =>  distance <= 1 (grid over the box, exact maximum 1 at the corner).
  2. Degeneracy: on random point sets with pairwise distances > 1, removing the lowest point each time, it never has more than
     6 remaining neighbours within sqrt3; the greedy 7-colouring's largest class has size >= N/7 and pairwise distances > sqrt3.
  3. Hexagon scheme of the posted answer (side 1/2, centres on the lattice of x = (3, sqrt3)/4, y = (0, sqrt3)/2, colours = cosets
     of the lattice of a = 3x - y, b = 2y + x): the least distance between two same-coloured hexagons is below sqrt3 (exact polygon
     distance), with an explicit pair of points.
  4. Density: 1/(1+sqrt3)^2 < 1/7, so 7 colour classes of the required kind cannot cover the plane; (1+sqrt3)^2 > 7.
  5. Nine classes (cosets of 3L): the least distance between same-coloured hexagons is exactly sqrt3, attained only by
     facing parallel edges, so with half-open hexagons two points in different same-coloured cells are > sqrt3 apart.
MUTANT=1 uses 40 degrees in the lemma; MUTANT=2 uses 1/(1+sqrt3) as the density bound. Each must FAIL.
"""
from __future__ import annotations

import math
import os
import random
import sys

MUTANT = int(os.environ.get("MUTANT", "0"))
R3 = math.sqrt(3)


def seg_dist(p, q, a, b) -> float:
    """distance between segments pq and ab (no intersections occur here)."""
    def pt_seg(c, u, v):
        ux, uy = v[0] - u[0], v[1] - u[1]
        t = max(0.0, min(1.0, ((c[0] - u[0]) * ux + (c[1] - u[1]) * uy) / (ux * ux + uy * uy)))
        return math.hypot(c[0] - u[0] - t * ux, c[1] - u[1] - t * uy)
    return min(pt_seg(p, a, b), pt_seg(q, a, b), pt_seg(a, p, q), pt_seg(b, p, q))


def hexagon(c, s=0.5):
    # vertices at angles 0, 60, ..., so that edge-sharing neighbours lie in directions 30, 90, 150 degrees
    return [(c[0] + s * math.cos(math.pi * k / 3), c[1] + s * math.sin(math.pi * k / 3)) for k in range(6)]


def poly_dist(P, Q):
    best, pair = 1e9, None
    for i in range(6):
        for j in range(6):
            d = seg_dist(P[i], P[(i + 1) % 6], Q[j], Q[(j + 1) % 6])
            if d < best:
                best = d
    return best


def main() -> int:
    ok = True
    ang = math.radians(40 if MUTANT == 1 else 30)
    worst = 0.0
    for i in range(201):
        for j in range(201):
            for k in range(61):
                r1 = 1 + (R3 - 1) * i / 200; r2 = 1 + (R3 - 1) * j / 200; t = ang * k / 60
                worst = max(worst, r1 * r1 + r2 * r2 - 2 * r1 * r2 * math.cos(t))
    print(f"1. max squared distance, radii in [1, sqrt3], angle <= {math.degrees(ang):.0f} deg: {worst:.12f}")
    ok &= worst <= 1 + 1e-12

    rng = random.Random(4)
    deg_ok = colour_ok = True
    for trial in range(300):
        P = []
        box = rng.uniform(3, 12)
        for _ in range(4000):
            q = (rng.uniform(0, box), rng.uniform(0, box))
            if all(math.dist(q, a) > 1 for a in P):
                P.append(q)
        order, rest = [], sorted(P, key=lambda p: (p[1], p[0]))
        maxdeg = 0
        for i, p in enumerate(rest):
            later = [q for q in rest[i + 1:] if math.dist(p, q) <= R3]
            maxdeg = max(maxdeg, len(later))
        deg_ok &= maxdeg <= 6
        colour = {}
        for i in range(len(rest) - 1, -1, -1):
            p = rest[i]
            used = {colour[q] for q in rest[i + 1:] if math.dist(p, q) <= R3}
            colour[p] = min(c for c in range(7) if c not in used)
        classes = [[p for p in rest if colour[p] == c] for c in range(7)]
        big = max(classes, key=len)
        colour_ok &= 7 * len(big) >= len(P) and all(math.dist(a, b) > R3 for i, a in enumerate(big) for b in big[:i])
    print(f"2. lowest point has <= 6 later neighbours within sqrt3 (300 random sets): {deg_ok}; class >= N/7, spacing > sqrt3: {colour_ok}")
    ok &= deg_ok and colour_ok

    x = (0.75, R3 / 4); y = (0.0, R3 / 2)
    a = (3 * x[0] - y[0], 3 * x[1] - y[1]); b = (2 * y[0] + x[0], 2 * y[1] + x[1])
    H0 = hexagon((0, 0))
    best = 1e9
    for m in range(-2, 3):
        for n in range(-2, 3):
            if (m, n) == (0, 0):
                continue
            c = (m * a[0] + n * b[0], m * a[1] + n * b[1])
            best = min(best, poly_dist(H0, hexagon(c)))
    # explicit pair: vertex of H0 nearest the hexagon at a, and the nearest point of that hexagon
    Ha = hexagon(a)
    print(f"3. posted scheme: |a| = {math.hypot(*a):.6f}, least distance between same-coloured hexagons = {best:.6f} (sqrt3 = {R3:.6f})")
    v0 = H0[0]; va = Ha[3]
    print(f"   e.g. vertices {tuple(round(t, 4) for t in v0)} and {tuple(round(t, 4) for t in va)} at distance {math.dist(v0, va):.6f}")
    ok &= best < R3

    best9, arg9 = 1e9, None
    for m in range(-3, 4):
        for n in range(-3, 4):
            if (m, n) == (0, 0):
                continue
            c = (3 * (m * x[0] + n * y[0]), 3 * (m * x[1] + n * y[1]))
            d = poly_dist(H0, hexagon(c))
            if d < best9 - 1e-12:
                best9, arg9 = d, [(m, n)]
            elif abs(d - best9) <= 1e-12:
                arg9.append((m, n))
    edge_normal = all(math.isclose(abs(math.degrees(math.atan2(*reversed((3 * (m * x[0] + n * y[0]), 3 * (m * x[1] + n * y[1]))))) % 60), 30, abs_tol=1e-9) for m, n in arg9)
    print(f"5. nine classes (3L): least distance {best9:.12f} (sqrt3 = {R3:.12f}), attained by {len(arg9)} neighbours, all across edges: {edge_normal}")
    ok &= abs(best9 - R3) < 1e-12 and edge_normal and len(arg9) == 6

    dens = 1 / (1 + R3) if MUTANT == 2 else 1 / (1 + R3) ** 2
    print(f"4. density bound {dens:.6f} vs 1/7 = {1 / 7:.6f}; (1+sqrt3)^2 = {(1 + R3) ** 2:.6f}")
    ok &= dens < 1 / 7
    print("PASS" if ok else "FAIL")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
