"""Second, independent decision of which R_n (n <= 19) have an admissible tiling.

Shares no code or method with src/frame.c (skyline search in C). Exact-cover model in Z3:
one Boolean per placement (size k < n, orientation, lower-left corner); each cell covered by
exactly one chosen placement; each size used at most once. SAT gives a tiling (checked with
verify/check.py); UNSAT is a solver proof that none exists.

Usage: small_sat.py n1 n2 ...   (one line per n: SAT/UNSAT and time)
"""

from __future__ import annotations

import sys
import time
from pathlib import Path

from z3 import AtMost, Bool, If, PbEq, Solver, Sum, is_true, sat, unsat

sys.path.insert(0, str(Path(__file__).resolve().parent))
from check import check


def decide(n: int) -> tuple[str, float]:
    W, H = n + 1, n
    placements = []  # (var, k, w, h, x, y)
    for k in range(1, n):
        for w, h in {(k + 1, k), (k, k + 1)}:
            for x in range(W - w + 1):
                for y in range(H - h + 1):
                    placements.append((Bool(f"p{k}_{w}_{x}_{y}"), k, w, h, x, y))
    s = Solver()
    cover: dict[tuple[int, int], list] = {
        (x, y): [] for x in range(W) for y in range(H)
    }
    by_size: dict[int, list] = {}
    for p in placements:
        var, k, w, h, x, y = p
        by_size.setdefault(k, []).append(var)
        for xx in range(x, x + w):
            for yy in range(y, y + h):
                cover[(xx, yy)].append(var)
    for cell, vs in cover.items():
        if not vs:  # a cell no piece can cover: no tiling
            return "UNSAT (uncoverable cell)", 0.0
        s.add(PbEq([(v, 1) for v in vs], 1))
    for k, vs in by_size.items():
        s.add(AtMost(*vs, 1))
    # Symmetry breaking. The rectangle's four symmetries (identity, two reflections, half-turn) act
    # transitively on its corners, so every tiling has an image whose bottom-left corner piece is at
    # least as large as the pieces at the other three corners. Each corner is covered by exactly one
    # placement, so its piece size is the weighted sum below.
    def corner_size(cx: int, cy: int):
        return Sum([If(var, k, 0) for var, k, w, h, x, y in placements if x <= cx < x + w and y <= cy < y + h])
    c00 = corner_size(0, 0)
    for c in ((W - 1, 0), (0, H - 1), (W - 1, H - 1)):
        s.add(c00 >= corner_size(*c))
    t0 = time.time()
    r = s.check()
    dt = time.time() - t0
    if r == sat:
        m = s.model()
        lines = ["SOL"] + [
            f"{k} {w} {h} {x} {y}"
            for var, k, w, h, x, y in placements
            if is_true(m.eval(var))
        ]
        err = check(lines, W, H)
        return ("SAT, tiling VALID" if err is None else f"SAT but INVALID: {err}"), dt
    return ("UNSAT" if r == unsat else "UNKNOWN"), dt


def main() -> None:
    for n in map(int, sys.argv[1:]):
        verdict, dt = decide(n)
        print(f"n={n}: {verdict} ({dt:.1f} s)", flush=True)


if __name__ == "__main__":
    main()
