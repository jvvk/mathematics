"""Independent check for slab tilings (Friedman, Math Magic, December 2001; unsolved problem 6).

A k-slab is a k x ik x jk box (i, j >= 1), in any orientation. Can an a x b x c box be tiled by one
k-slab for each k = 1..n? This program decides it by a direct search over placements, with no solver:
the first empty cell (in lexicographic order) must be the corner of the box that covers it, so each
step tries every unused slab, every size and every orientation with its corner there. A step is
pruned unless the empty volume can still be written as a sum of volumes of the unused slabs.
Usage: python3 slab_search.py n a b c      (prints a tiling or "impossible")
"""
from __future__ import annotations

import sys
from functools import lru_cache
from itertools import permutations


def tile(n: int, dims: tuple[int, int, int]):
    A, B, C = dims
    occ = bytearray(A * B * C)
    idx = lambda x, y, z: (x * B + y) * C + z
    sizes = {k: sorted({tuple(p) for i in range(1, max(dims) // k + 1) for j in range(i, max(dims) // k + 1)
                        for p in permutations((k, i * k, j * k))
                        if p[0] <= A and p[1] <= B and p[2] <= C}) for k in range(1, n + 1)}
    vols = {k: sorted({a * b * c for a, b, c in sizes[k]}) for k in sizes}

    @lru_cache(None)
    def feasible(rest: frozenset, vol: int) -> bool:
        if not rest:
            return vol == 0
        k = min(rest)
        return any(v <= vol and feasible(rest - {k}, vol - v) for v in vols[k])

    placed: list = []

    def first_empty(start: int) -> int:
        i = occ.find(0, start)
        return i

    def fits(x, y, z, a, b, c) -> bool:
        if x + a > A or y + b > B or z + c > C:
            return False
        for u in range(x, x + a):
            for v in range(y, y + b):
                base = idx(u, v, z)
                if any(occ[base:base + c]):
                    return False
        return True

    def paint(x, y, z, a, b, c, val) -> None:
        for u in range(x, x + a):
            for v in range(y, y + b):
                base = idx(u, v, z)
                occ[base:base + c] = bytes([val]) * c

    def rec(rest: frozenset, empty: int, start: int):
        cell = first_empty(start)
        if cell < 0:
            return list(placed) if not rest else None
        if not rest or not feasible(rest, empty):
            return None
        x, r = divmod(cell, B * C)
        y, z = divmod(r, C)
        for k in sorted(rest):
            for a, b, c in sizes[k]:
                if fits(x, y, z, a, b, c):
                    paint(x, y, z, a, b, c, 1)
                    placed.append((k, (x, y, z), (a, b, c)))
                    got = rec(rest - {k}, empty - a * b * c, cell)
                    if got:
                        return got
                    placed.pop()
                    paint(x, y, z, a, b, c, 0)
        return None

    return rec(frozenset(range(1, n + 1)), A * B * C, 0)


def check_tiling(n, dims, tiling) -> None:
    A, B, C = dims
    seen = set()
    assert sorted(k for k, _, _ in tiling) == list(range(1, n + 1))
    for k, (x, y, z), (a, b, c) in tiling:
        s = sorted((a, b, c))
        assert k in s and all(d % k == 0 for d in s), (k, a, b, c)
        for u in range(x, x + a):
            for v in range(y, y + b):
                for w in range(z, z + c):
                    assert 0 <= u < A and 0 <= v < B and 0 <= w < C and (u, v, w) not in seen
                    seen.add((u, v, w))
    assert len(seen) == A * B * C


if __name__ == "__main__":
    n, *d = map(int, sys.argv[1:5])
    t = tile(n, tuple(d))
    if t:
        check_tiling(n, tuple(d), t)
        print("tiling", t)
    else:
        print("impossible")
