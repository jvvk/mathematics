"""Independent recheck: tilings of the n x n square by translates of a cell set P and of g(P), for one fixed
second orientation g (the half-turn or one of the four reflections). Shares no code with ../check.py,
../verify.py or ../tilesq.c: own cell sets, own symmetries, own exact cover.

Claims checked (Theorems 1 and 2 of the note, for small primes):
  * p = 3, 5: every p-cell set P (connected or not) that fits in the board, every g: only bars tile.
  * p = 7: every connected 7-cell set (760 fixed heptominoes, OEIS A001168), every g: only bars tile.
  * p = 2, half-turn: every 2-cell set: only dominoes tile.
  * p = 2, mirror reflection: the diagonal pair does tile (why Theorem 2 needs p odd).
  * n = 4, half-turn: the L-tetromino tiles; translations alone do not suffice for it (composite control).

    timeout 600 nice -n 15 ~/.venvs/main/bin/python recheck.py
"""

from __future__ import annotations

import itertools
import sys
from collections.abc import Callable

Cell = tuple[int, int]
Shape = frozenset[Cell]

# The five involutions of the square used as a second orientation, as maps of the plane.
INVOLUTIONS: dict[str, Callable[[Cell], Cell]] = {
    "half-turn": lambda c: (-c[0], -c[1]),
    "mirror x": lambda c: (-c[0], c[1]),
    "mirror y": lambda c: (c[0], -c[1]),
    "diagonal": lambda c: (c[1], c[0]),
    "antidiagonal": lambda c: (-c[1], -c[0]),
}


def norm(s) -> Shape:
    s = list(s)
    mx, my = min(x for x, _ in s), min(y for _, y in s)
    return frozenset((x - mx, y - my) for x, y in s)


def placements(shape: Shape, n: int) -> list[int]:
    w, h = max(x for x, _ in shape) + 1, max(y for _, y in shape) + 1
    out = []
    for a in range(n - w + 1):
        for b in range(n - h + 1):
            out.append(sum(1 << ((x + a) * n + (y + b)) for x, y in shape))
    return out


def tiles(masks: list[int], n: int, overlap_ok: bool = False) -> bool:
    """Exact cover of the n x n board by the given placement masks (repetition allowed)."""
    full = (1 << (n * n)) - 1
    by_cell: list[list[int]] = [[] for _ in range(n * n)]
    for m in masks:
        by_cell[(m & -m).bit_length() - 1].append(
            m
        )  # index each placement by its lowest cell

    def go(cov: int) -> bool:
        if cov == full:
            return True
        free = ~cov & full
        i = (free & -free).bit_length() - 1
        for m in by_cell[i]:
            if overlap_ok or not (m & cov):
                if go(cov | m):
                    return True
        return False

    return go(0)


def is_bar(s: Shape) -> bool:
    xs, ys = {x for x, _ in s}, {y for _, y in s}
    return (len(xs) == 1 or len(ys) == 1) and norm(s) in (
        frozenset((0, k) for k in range(len(s))),
        frozenset((k, 0) for k in range(len(s))),
    )


def tilers(
    shapes, n: int, g: Callable[[Cell], Cell], overlap_ok: bool = False
) -> list[Shape]:
    found = []
    for s in shapes:
        t = norm(g(c) for c in s)
        if tiles(placements(s, n) + placements(t, n), n, overlap_ok):
            found.append(s)
    return found


def all_sets(p: int) -> list[Shape]:
    """Every p-cell subset of the p x p board, up to translation."""
    board = [(x, y) for x in range(p) for y in range(p)]
    return sorted({norm(c) for c in itertools.combinations(board, p)}, key=sorted)


def connected_fixed(p: int) -> list[Shape]:
    shapes = {frozenset({(0, 0)})}
    for _ in range(p - 1):
        shapes = {
            norm(s | {(x + dx, y + dy)})
            for s in shapes
            for x, y in s
            for dx, dy in ((1, 0), (-1, 0), (0, 1), (0, -1))
            if (x + dx, y + dy) not in s
        }
    return sorted(shapes, key=sorted)


def run(
    overlap_ok: bool = False, half: Callable[[Cell], Cell] = INVOLUTIONS["half-turn"]
) -> int:
    k = 0
    inv = {**INVOLUTIONS, "half-turn": half}
    for p in (3, 5):
        sets = all_sets(p)
        for name, g in inv.items():
            bad = [s for s in tilers(sets, p, g, overlap_ok) if not is_bar(s)]
            assert not bad, f"p={p}, {name}: non-bar {sorted(bad[0])}"
            k += 1
        print(f"p={p}: {len(sets)} cell sets x 5 involutions, only bars", flush=True)
    hept = connected_fixed(7)
    assert len(hept) == 760, len(hept)
    for name, g in inv.items():
        found = tilers(hept, 7, g, overlap_ok)
        assert found and all(is_bar(s) for s in found), (
            f"p=7, {name}: {[sorted(s) for s in found][:1]}"
        )
        k += 1
    print("p=7: 760 fixed heptominoes x 5 involutions, only bars", flush=True)
    two = all_sets(2)
    assert all(is_bar(s) for s in tilers(two, 2, half, overlap_ok)), (
        "p=2 half-turn: non-domino"
    )
    diag = frozenset({(0, 0), (1, 1)})
    assert diag in tilers(two, 2, inv["mirror x"], overlap_ok), (
        "p=2 diagonal pair should tile"
    )
    ell = frozenset({(0, 0), (1, 0), (2, 0), (0, 1)})
    assert tilers([ell], 4, half, overlap_ok) == [ell], (
        "n=4: L-tetromino with half-turns should tile"
    )
    assert not tilers([ell], 4, lambda c: c, overlap_ok), (
        "n=4: L-tetromino translations only should not tile"
    )
    print(
        "controls: p=2 half-turn only dominoes; p=2 diagonal pair tiles with a mirror; n=4 L tiles only with half-turns"
    )
    return k + 4


if __name__ == "__main__":
    print(f"positive: {run()} checks passed\n", flush=True)
    mutants = {
        "overlaps allowed": dict(overlap_ok=True),
        "half-turn replaced by the identity": dict(half=lambda c: c),
        "half-turn replaced by a quarter-turn": dict(half=lambda c: (-c[1], c[0])),
    }
    for name, kw in mutants.items():
        try:
            run(**kw)
        except AssertionError as e:
            print(f"rejected mutant: {name} ({e})\n", flush=True)
        else:
            sys.exit(f"UNDETECTED MUTANT: {name}")
    print(f"all {len(mutants)} mutants rejected")
