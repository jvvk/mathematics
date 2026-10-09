"""Slab tilings (Math Magic, December 2001; unsolved no. 6): a k-slab is a k x ik x jk box. Tile the
s x s x s cube (or an a x b x c box) with exactly one k-slab for each k = 1..n. CP-SAT exact cover.
Usage: python3 slabs.py N A B C [SECONDS] [--combos]   (A = B = C for a cube; --combos splits by slab sizes)
"""

from __future__ import annotations

import json
import sys
from pathlib import Path

from ortools.sat.python import cp_model

ROOT = Path(__file__).resolve().parent


def size_combos(n: int, side: int) -> list[list[tuple[int, int]]]:
    """For a cube: every choice of face (a, b), a <= b multiples of k up to side, one per k, whose volumes
    k*a*b add up to side^3."""
    target = side**3
    opts = {k: [(a, b) for a in range(k, side + 1, k) for b in range(a, side + 1, k)] for k in range(1, n + 1)}
    best = {k: k * max(a * b for a, b in opts[k]) for k in opts}
    out: list[list[tuple[int, int]]] = []

    def rec(k: int, left: int, cur: list) -> None:
        if k == 0:
            if left == 0:
                out.append(cur[::-1])
            return
        if left > sum(best[q] for q in range(1, k + 1)) or left < 0:
            return
        for a, b in opts[k]:
            rec(k - 1, left - k * a * b, cur + [(a, b)])

    rec(n, target, [])
    return out


def solve(n: int, dims: tuple[int, int, int], seconds: float, faces: list | None = None) -> tuple[str, list]:
    A, B, C = dims
    model = cp_model.CpModel()
    cells: dict[tuple[int, int, int], list] = {
        (x, y, z): [] for x in range(A) for y in range(B) for z in range(C)
    }
    opts = []
    for k in range(1, n + 1):
        mine = []
        shapes = set()
        pairs = [faces[k - 1]] if faces else [(i * k, j * k) for i in range(1, max(dims) // k + 1) for j in range(1, max(dims) // k + 1)]
        for fa, fb in pairs:
            for i, j in {(fa // k, fb // k), (fb // k, fa // k)}:
                d = (k, i * k, j * k)
                for p in {(d[0], d[1], d[2]), (d[1], d[0], d[2]), (d[1], d[2], d[0])}:
                    shapes.add(p)
        # volume filter: the slabs must add up to the box; any single slab must fit
        for w, h, t in shapes:
            if w > A or h > B or t > C:
                continue
            for x in range(A - w + 1):
                for y in range(B - h + 1):
                    for z in range(C - t + 1):
                        v = model.NewBoolVar("")
                        mine.append(v)
                        opts.append((v, (k, x, y, z, w, h, t)))
                        for a in range(x, x + w):
                            for b in range(y, y + h):
                                for c in range(z, z + t):
                                    cells[(a, b, c)].append(v)
        if not mine:
            return "impossible", []
        model.AddExactlyOne(mine)
    for vs in cells.values():
        model.AddExactlyOne(vs)
    s = cp_model.CpSolver()
    s.parameters.num_workers = 1
    s.parameters.max_time_in_seconds = seconds
    st = s.Solve(model)
    name = {
        cp_model.OPTIMAL: "found",
        cp_model.FEASIBLE: "found",
        cp_model.INFEASIBLE: "impossible",
    }.get(st, "unknown")
    return name, ([r for v, r in opts if s.Value(v)] if name == "found" else [])


def check(n: int, dims: tuple[int, int, int], slabs: list) -> None:
    """Independent check: one slab per k, dimensions k x ik x jk in some order, exact cover of the box."""
    assert sorted(r[0] for r in slabs) == list(range(1, n + 1))
    seen: set = set()
    for k, x, y, z, w, h, t in slabs:
        e = sorted((w, h, t))
        assert k in (w, h, t) and all(v % k == 0 for v in e)
        assert (
            0 <= x
            and x + w <= dims[0]
            and 0 <= y
            and y + h <= dims[1]
            and 0 <= z
            and z + t <= dims[2]
        )
        box = {
            (a, b, c)
            for a in range(x, x + w)
            for b in range(y, y + h)
            for c in range(z, z + t)
        }
        assert not box & seen
        seen |= box
    assert len(seen) == dims[0] * dims[1] * dims[2]


if __name__ == "__main__":
    n = int(sys.argv[1])
    dims = (int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]))
    sec = float(sys.argv[5]) if len(sys.argv) > 5 and not sys.argv[5].startswith("-") else 60
    if "--combos" in sys.argv and len(set(dims)) == 1:
        combos = size_combos(n, dims[0])
        print(f"{len(combos)} size combinations", flush=True)
        st, slabs = "impossible", []
        for f in combos:
            st1, sl = solve(n, dims, sec, faces=f)
            if sl:
                st, slabs = st1, sl
                break
            if st1 == "unknown":
                st = "unknown"
    else:
        st, slabs = solve(n, dims, sec)
    if slabs:
        check(n, dims, slabs)
        (ROOT / "data" / f"slabs_{n}_{'x'.join(map(str, dims))}.json").write_text(
            json.dumps({"n": n, "dims": dims, "slabs": slabs})
        )
    print(f"n={n} box={dims}: {st}", flush=True)
