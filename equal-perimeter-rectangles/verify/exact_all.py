"""Exact rerun of the whole search (no floating point). For every mosaic floorplan with
n <= N rooms: solve the equal-semi-perimeter system over Q (square side 1), record whether it
is singular, keep realisations with all sides > 0, and compare dissections geometrically under
the 8 symmetries of the unit square (normalising the side to 1 removes scaling).
Outputs: per-n counts of distinct dissections (must equal OEIS A100664) and of dissections
with pairwise non-congruent rectangles."""

from __future__ import annotations

import sys
from fractions import Fraction as Fr

from floorplans import all_floorplans

A100664 = [1, 1, 2, 6, 16, 50, 177, 664, 2532]


def solve_exact(fp):
    V = max(r[1] for r in fp) - 1
    H = max(r[3] for r in fp) - 1
    n = len(fp)
    m = V + H + 1
    rows = []
    for x1, x2, y1, y2 in fp:
        row = [Fr(0)] * (m + 1)  # last entry: right-hand side
        for idx, coef, is_x in ((x2, 1, True), (x1, -1, True), (y2, 1, False), (y1, -1, False)):
            top = V + 1 if is_x else H + 1
            if idx == 0:
                continue
            if idx == top:
                row[m] -= coef
            else:
                row[(idx - 1) if is_x else (V + idx - 1)] += coef
        row[m - 1] = Fr(-1)  # -s
        rows.append(row)
    # Gauss-Jordan over Q
    piv_row = 0
    where = [-1] * m
    for col in range(m):
        p = next((r for r in range(piv_row, n) if rows[r][col] != 0), None)
        if p is None:
            continue
        rows[piv_row], rows[p] = rows[p], rows[piv_row]
        pv = rows[piv_row][col]
        rows[piv_row] = [v / pv for v in rows[piv_row]]
        for r in range(n):
            if r != piv_row and rows[r][col] != 0:
                f = rows[r][col]
                rows[r] = [a - f * b for a, b in zip(rows[r], rows[piv_row])]
        where[col] = piv_row
        piv_row += 1
    if piv_row < m:
        return None, V, H  # singular
    sol = [rows[where[c]][m] for c in range(m)]
    return sol, V, H


def rects(fp, sol, V, H):
    X = [Fr(0)] + sol[:V] + [Fr(1)]
    Y = [Fr(0)] + sol[V:V + H] + [Fr(1)]
    return [(X[a], X[b], Y[c], Y[d]) for a, b, c, d in fp]


def canon(R):
    best = None
    for k in range(8):
        S = []
        for x1, x2, y1, y2 in R:
            def t(x, y):
                if k & 4:
                    x, y = y, x
                if k & 1:
                    x = 1 - x
                if k & 2:
                    y = 1 - y
                return x, y
            (a, c), (b, d) = t(x1, y1), t(x2, y2)
            S.append((min(a, b), max(a, b), min(c, d), max(c, d)))
        S = tuple(sorted(S))
        best = S if best is None or S < best else best
    return best


if __name__ == "__main__":
    N = int(sys.argv[1])
    for n, lev in enumerate(all_floorplans(N), 1):
        sing = 0
        dissections, noncong = set(), set()
        for fp in lev:
            sol, V, H = solve_exact(fp)
            if sol is None:
                sing += 1
                continue
            R = rects(fp, sol, V, H)
            if any(r[1] <= r[0] or r[3] <= r[2] for r in R):
                continue
            c = canon(R)
            dissections.add(c)
            shapes = [tuple(sorted((r[1] - r[0], r[3] - r[2]))) for r in R]
            if len(set(shapes)) == len(shapes):
                noncong.add(c)
        ok = "OK" if len(dissections) == A100664[n - 1] else "MISMATCH"
        print(f"n={n}: floorplans {len(lev)}, singular {sing}, dissections {len(dissections)} "
              f"(A100664 {A100664[n - 1]} {ok}), pairwise non-congruent {len(noncong)}", flush=True)
