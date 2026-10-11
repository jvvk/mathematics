"""Certified lower bounds: in the regular n-gon of side 1 with all diagonals drawn, some cell other than the odd
central cell has area larger than the edge triangle, for the listed n.

Method.
1. Floating point (shapely): build the arrangement, find the largest cell that does not contain the centre.
2. Certificate (python-flint arb balls, 256 bits): recompute the cell's vertices as intersections of its supporting
   lines X cos(u t) + Y sin(u t) = R cos(v t) (t = pi/n, R = 1/(2 sin t)), shrink the polygon towards its centroid by
   the factor 1 - eps, and check that every side and diagonal leaves all shrunken vertices strictly on one side. Then
   the shrunken convex polygon meets no line of the arrangement, so it lies inside a single cell, whose area is at
   least (1 - eps)^2 times the computed area. Concurrent diagonals cannot break this: only strict signs at interior
   points are tested.
3. Compare with the edge triangle, area (1/4) tan(pi/n), also in arb.

MUTANT=1 skips the shrinking (eps = 0): lines through the candidate's vertices then give signs that cannot be
certified, and the run must fail. MUTANT=2 compares against twice the edge triangle, which must fail.
"""

import math
import os
import sys

from flint import arb, ctx
from shapely.geometry import LineString, Point, Polygon
from shapely.ops import polygonize, unary_union

ctx.prec = 256
MUTANT = os.environ.get("MUTANT", "0")
EPS = arb(1) / 10**6


def chords(n):
    """All sides and diagonals as (u, v): normal angle u t, offset R cos(v t); endpoints at (u -+ v) t."""
    out = set()
    for i in range(n):
        for j in range(i + 1, n):
            u, v = i + j, j - i  # endpoints 2i t and 2j t: u t = (i+j) t, v t = (j-i) t
            out.add((u, v))
    return sorted(out)


def float_cells(n):
    t = math.pi / n
    R = 1 / (2 * math.sin(t))
    P = [(R * math.cos(2 * k * t), R * math.sin(2 * k * t)) for k in range(n)]
    lines = [LineString([P[i], P[j]]) for i in range(n) for j in range(i + 1, n)]
    cells = list(polygonize(unary_union(lines)))
    return cells, R, t


def best_cell(n):
    cells, R, t = float_cells(n)
    centre = Point(0, 0)
    eligible = [c for c in cells if not (n % 2 == 1 and c.contains(centre))]
    return max(eligible, key=lambda c: c.area), R, t


def supporting(n, poly, R, t):
    """For each edge of the float polygon, the chord (u, v) whose line contains it."""
    cs = chords(n)
    coords = list(poly.exterior.coords)[:-1]
    if Polygon(coords).exterior.is_ccw is False:
        coords = coords[::-1]
    sup = []
    for k in range(len(coords)):
        (x1, y1), (x2, y2) = coords[k], coords[(k + 1) % len(coords)]
        mx, my = (x1 + x2) / 2, (y1 + y2) / 2
        best = min(
            cs,
            key=lambda c: abs(
                mx * math.cos(c[0] * t)
                + my * math.sin(c[0] * t)
                - R * math.cos(c[1] * t)
            ),
        )
        sup.append(best)
    # merge collinear consecutive edges (same supporting chord)
    merged = [s for k, s in enumerate(sup) if s != sup[k - 1]]
    return merged or sup


def certify(n):
    poly, Rf, tf = best_cell(n)
    t = arb.pi() / n
    R = 1 / (2 * t.sin())
    sup = supporting(n, poly, Rf, tf)

    def line(c):
        u, v = c
        return (u * t).cos(), (u * t).sin(), R * (v * t).cos()

    L = [line(c) for c in sup]
    V = []
    for k in range(len(L)):
        a1, b1, c1 = L[k - 1]
        a2, b2, c2 = L[k]
        det = a1 * b2 - a2 * b1
        V.append(((c1 * b2 - c2 * b1) / det, (a1 * c2 - a2 * c1) / det))
    m = len(V)
    area = (
        sum(V[k][0] * V[(k + 1) % m][1] - V[(k + 1) % m][0] * V[k][1] for k in range(m))
        / 2
    )
    assert area > 0, "orientation"
    gx = sum(p[0] for p in V) / m
    gy = sum(p[1] for p in V) / m
    eps = arb(0) if MUTANT == "1" else EPS
    W = [(gx + (1 - eps) * (p[0] - gx), gy + (1 - eps) * (p[1] - gy)) for p in V]
    # every side and diagonal: all shrunken vertices strictly on one side
    for c in chords(n):
        a, b, off = line(c)
        signs = set()
        for x, y in W:
            val = a * x + b * y - off
            if val > 0:
                signs.add(1)
            elif val < 0:
                signs.add(-1)
            else:
                raise AssertionError(f"n={n}: sign of chord {c} not certified")
        assert len(signs) == 1, f"n={n}: chord {c} crosses the candidate"
    lower = (1 - eps) ** 2 * area
    edge = (t.tan()) / 4
    target = 2 * edge if MUTANT == "2" else edge
    return (
        lower,
        edge,
        lower > target,
        poly.area,
        len(sup),
        math.hypot(*poly.centroid.coords[0]),
        Rf,
    )


def main():
    ns = [int(a) for a in sys.argv[1:]] or [9, 12, 15, 20, 25, 31, 40]
    ok = True
    for n in ns:
        lower, edge, win, fa, sides, r, R = certify(n)
        print(
            f"n={n}: certified cell area >= {lower.mid().str(8)} (float {fa:.6f}, {sides} sides, centroid r={r:.2f}, "
            f"R={R:.2f}); edge triangle {edge.mid().str(8)}; n*area >= {(n * lower).mid().str(5)}: "
            f"{'LARGER' if win else 'not larger'}"
        )
        ok &= win
    print("PASS" if ok else "FAIL")
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
