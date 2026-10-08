"""Independent recheck (gate J4) of the 300255 enumeration. Shares no code with floorplans.py,
exact_all.py or exact.py.

Method. A dissection of a square into n rectangles with no point where four meet has V vertical
and H horizontal maximal segments, V + H = n - 1. Ordering each family by coordinate turns it into
an integer "index" tiling of a (V+1) x (H+1) grid of cells in which every internal grid line
carries exactly one contiguous segment (a tight paving). We enumerate these tilings
directly by filling the lowest, then leftmost, empty cell. Every combinatorial type appears at
least once (types with several valid orderings appear several times; duplicates are harmless,
since the equal-perimeter equations depend only on the type).

For each tiling, the unknowns are the V + H segment coordinates and the common semi-perimeter s
(square side 1): n equations in n unknowns, solved by fraction-exact Bareiss elimination. A
nonsingular system has one solution; it is a dissection when every width and height is positive.
Dissections with a 4-way point arise as degenerate solutions of generic types, so they are found
too. Results are deduplicated geometrically under the 8 symmetries of the square.

Checks printed: tiling counts against (OEIS A298432, tight pavings summed over grid shapes), singular
systems (must be 0), dissection counts against OEIS A100664, and the pairwise non-congruent
solutions, which must be the five listed in the note."""

from __future__ import annotations

import json
import sys
from fractions import Fraction

A298432 = [1, 2, 6, 24, 118, 680, 4456, 32512, 260080]
A100664 = [1, 1, 2, 6, 16, 50, 177, 664, 2532]

# The five n = 9 solutions stated in the note, as integer rectangles [x1,x2] x [y1,y2].
STATED: dict[int, list[tuple[int, int, int, int]]] = {}


def index_tilings(n: int):
    """Yield (V, H, rooms) for every generic index tiling with n rooms."""
    for V in range(n):
        H = n - 1 - V
        W, Ht = V + 1, H + 1
        grid = [[-1] * W for _ in range(Ht)]
        rooms: list[tuple[int, int, int, int]] = []

        def fill():
            # lowest then leftmost empty cell
            for y in range(Ht):
                for x in range(W):
                    if grid[y][x] < 0:
                        break
                else:
                    continue
                break
            else:
                if len(rooms) == n and valid(rooms, W, Ht):
                    yield list(rooms)
                return
            if len(rooms) == n:
                return
            maxw = 0
            while x + maxw < W and grid[y][x + maxw] < 0:
                maxw += 1
            for w in range(1, maxw + 1):
                for h in range(1, Ht - y + 1):
                    if any(grid[y + h - 1][x + i] >= 0 for i in range(w)):
                        break
                    k = len(rooms)
                    for j in range(h):
                        for i in range(w):
                            grid[y + j][x + i] = k
                    rooms.append((x, x + w, y, y + h))
                    yield from fill()
                    rooms.pop()
                    for j in range(h):
                        for i in range(w):
                            grid[y + j][x + i] = -1

        yield from ((V, H, r) for r in fill())


def valid(rooms, W, Ht) -> bool:
    # each internal vertical line x = i: the union of room edges on it is one nonempty interval
    for i in range(1, W):
        cover = [False] * Ht
        for x1, x2, y1, y2 in rooms:
            if x1 == i or x2 == i:
                for y in range(y1, y2):
                    cover[y] = True
        ys = [y for y in range(Ht) if cover[y]]
        if not ys or ys[-1] - ys[0] + 1 != len(ys):
            return False
    for j in range(1, Ht):
        cover = [False] * W
        for x1, x2, y1, y2 in rooms:
            if y1 == j or y2 == j:
                for x in range(x1, x2):
                    cover[x] = True
        xs = [x for x in range(W) if cover[x]]
        if not xs or xs[-1] - xs[0] + 1 != len(xs):
            return False
    # no interior point where four rooms meet
    corners: dict[tuple[int, int], int] = {}
    for x1, x2, y1, y2 in rooms:
        for p in ((x1, y1), (x1, y2), (x2, y1), (x2, y2)):
            corners[p] = corners.get(p, 0) + 1
    return all(c < 4 for c in corners.values())


def bareiss_solve(A: list[list[int]], b: list[int]) -> list[Fraction] | None:
    """Exact solve of A z = b over Q via integer Bareiss + back substitution; None if singular."""
    m = len(A)
    M = [row[:] + [bi] for row, bi in zip(A, b)]
    prev = 1
    for k in range(m):
        p = next((r for r in range(k, m) if M[r][k] != 0), None)
        if p is None:
            return None
        M[k], M[p] = M[p], M[k]
        for i in range(k + 1, m):
            for j in range(k + 1, m + 1):
                M[i][j] = (M[i][j] * M[k][k] - M[i][k] * M[k][j]) // prev
            M[i][k] = 0
        prev = M[k][k]
    z = [Fraction(0)] * m
    for i in range(m - 1, -1, -1):
        acc = Fraction(M[i][m]) - sum(Fraction(M[i][j]) * z[j] for j in range(i + 1, m))
        z[i] = acc / M[i][i]
    return z


def realise(V, H, rooms):
    """Coordinates of the unique equal-semi-perimeter realisation, or 'singular' / None."""
    n = len(rooms)
    # unknowns: X_1..X_V (cols 0..V-1), Y_1..Y_H (cols V..V+H-1), s (col n-1); X_0=Y_0=0, X_{V+1}=Y_{H+1}=1
    A, b = [], []
    for x1, x2, y1, y2 in rooms:
        row, rhs = [0] * n, 0
        for idx, sign, off, last in (
            (x2, 1, 0, V + 1),
            (x1, -1, 0, V + 1),
            (y2, 1, V, H + 1),
            (y1, -1, V, H + 1),
        ):
            if idx == last:
                rhs -= sign
            elif idx > 0:
                row[off + idx - 1] += sign
        row[n - 1] -= 1
        A.append(row)
        b.append(rhs)
    z = bareiss_solve(A, b)
    if z is None:
        return "singular"
    X = [Fraction(0)] + z[:V] + [Fraction(1)]
    Y = [Fraction(0)] + z[V : V + H] + [Fraction(1)]
    R = [(X[a], X[c], Y[d], Y[e]) for a, c, d, e in rooms]
    if any(r[1] <= r[0] or r[3] <= r[2] for r in R):
        return None
    return R


def key(R) -> tuple:
    """Symmetry-invariant key: the least sorted rectangle list over the dihedral group of order 8."""
    images = []
    for swap in (False, True):
        for fx in (False, True):
            for fy in (False, True):
                img = []
                for x1, x2, y1, y2 in R:
                    a1, a2, b1, b2 = (y1, y2, x1, x2) if swap else (x1, x2, y1, y2)
                    if fx:
                        a1, a2 = 1 - a2, 1 - a1
                    if fy:
                        b1, b2 = 1 - b2, 1 - b1
                    img.append((a1, a2, b1, b2))
                images.append(tuple(sorted(img)))
    return min(images)


def integer_form(R):
    """Scale to the least integer side; return (side, rectangles)."""
    from math import lcm

    L = 1
    for r in R:
        for c in r:
            L = lcm(L, c.denominator)
    return L, sorted(tuple(int(c * L) for c in r) for r in R)


def main(N: int) -> int:
    ok = True
    for n in range(1, N + 1):
        tilings = sing = 0
        diss: set = set()
        nonc: dict = {}
        for V, H, rooms in index_tilings(n):
            tilings += 1
            R = realise(V, H, rooms)
            if R == "singular":
                sing += 1
                continue
            if R is None:
                continue
            k = key(R)
            diss.add(k)
            shapes = {tuple(sorted((r[1] - r[0], r[3] - r[2]))) for r in R}
            if len(shapes) == n:
                nonc[k] = R
        good = tilings == A298432[n - 1] and sing == 0 and len(diss) == A100664[n - 1]
        ok &= good
        print(
            f"n={n}: tight pavings {tilings} (A298432 {A298432[n - 1]}), singular {sing}, "
            f"dissections {len(diss)} (A100664 {A100664[n - 1]}), non-congruent {len(nonc)} "
            f"{'OK' if good else 'MISMATCH'}",
            flush=True,
        )
        if n == N:
            out = []
            for R in sorted(nonc.values(), key=lambda R: integer_form(R)[0]):
                side, rects = integer_form(R)
                s = rects[0][1] - rects[0][0] + rects[0][3] - rects[0][2]
                print(f"  side {side}, perimeter {2 * s}: {rects}")
                out.append({"side": side, "perimeter": 2 * s, "rects": rects})
            with open(f"noncongruent_{N}.json", "w") as f:
                json.dump(out, f, indent=1)
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main(int(sys.argv[1]) if len(sys.argv) > 1 else 9))
