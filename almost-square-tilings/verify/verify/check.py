"""Independent checker for an almost-square dissection printed by src/frame.

Input: "SOL" then lines "k w h x y". Checks, cell by cell, that the pieces exactly tile the
W x H rectangle, that each piece is k x (k+1) in some orientation (the hole, k = -m, is m x (m+1)),
and that no positive size repeats. With n given (admissible mode), every piece must also be a genuine
almost-square of size 1 <= k < n (no holes, no zero-size pieces), with all sizes distinct.
"""

from __future__ import annotations

import sys


def check(lines: list[str], w: int, h: int, n: int | None = None) -> str | None:
    rows = [
        tuple(map(int, ln.split()))
        for ln in lines
        if ln.strip() and ln.strip() != "SOL"
    ]
    if any(len(r) != 5 for r in rows):
        return "malformed line"
    if n is not None:
        bad = [k for k, *_ in rows if not 1 <= k < n]
        if bad:
            return f"piece size {bad[0]} outside 1..{n - 1}"
    sizes = [k for k, *_ in rows if k > 0]
    if len(sizes) != len(set(sizes)):
        return "repeated size"
    grid = [[0] * w for _ in range(h)]
    for k, pw, ph, x, y in rows:
        a = abs(k)
        if a == 0 or sorted((pw, ph)) != [a, a + 1]:
            return f"piece {k} has shape {pw}x{ph}"
        if x < 0 or y < 0 or x + pw > w or y + ph > h:
            return f"piece {k} leaves the rectangle"
        for yy in range(y, y + ph):
            for xx in range(x, x + pw):
                grid[yy][xx] += 1
    bad = [(x, y) for y in range(h) for x in range(w) if grid[y][x] != 1]
    return f"cell {bad[0]} covered {grid[bad[0][1]][bad[0][0]]} times" if bad else None


def main() -> None:
    f, w, h = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])
    n = int(sys.argv[4]) if len(sys.argv) > 4 else None  # optional: admissible mode for R_n
    lines = [ln for ln in open(f).read().splitlines() if not ln.startswith("COUNT")]
    err = check(lines, w, h, n)
    print("VALID" if err is None else f"INVALID: {err}")
    sys.exit(0 if err is None else 1)


if __name__ == "__main__":
    main()
