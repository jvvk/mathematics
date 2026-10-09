"""Unfoldings of the d-cube up to symmetry, without enumerating labelled spanning trees.

A labelled spanning tree of the facet graph, up to the symmetry group of the cube (signed
permutations of the axes), is the same as a tree T on 2d vertices together with a perfect
matching M of its vertices ("opposite facets") that uses no edge of T, up to automorphisms of T.
(The group relabels the d opposite pairs freely and swaps each pair, so only the pairing matters.)
Each (T, M) is reduced to a canonical form with nauty: the tree edges plus one extra vertex of a
second colour joined to both ends of each matched pair. Each class is then rolled out into a
polycube exactly as in unfold.c.

Usage: gen_nets.py d outfile [--compare certfile]
  --compare checks that the polycubes, up to isometry, are exactly those in an earlier cert file.
"""

from __future__ import annotations

import itertools
import re
import sys

import networkx as nx
from pynauty import Graph, certificate


def matchings(V: int, adj: list[set[int]]):
    """Perfect matchings of {0..V-1} avoiding tree edges."""
    free = list(range(V))
    pairs: list[tuple[int, int]] = []

    def rec(rem: list[int]):
        if not rem:
            yield list(pairs)
            return
        a = rem[0]
        for k in range(1, len(rem)):
            b = rem[k]
            if b in adj[a]:
                continue
            pairs.append((a, b))
            yield from rec(rem[1:k] + rem[k + 1 :])
            pairs.pop()

    yield from rec(free)


def roll(d: int, adj: list[set[int]], facet: list[int]) -> list[tuple[int, ...]]:
    """Floor imprint of rolling the cube along the tree, facets labelled 2a (+e_a), 2a+1 (-e_a).
    World axis d-1 is vertical; the facet -e_{d-1} starts face down at the origin, identity
    orientation, as in unfold.c."""
    M = d - 1
    cells: list[tuple[int, ...]] = []
    root = facet.index(2 * M + 1)
    w = list(range(d)); s = [1] * d
    stack = [(root, -1, w, s, (0,) * M)]
    while stack:
        f, parent, w, s, pos = stack.pop()
        cells.append(pos)
        for g in adj[f]:
            if g == parent:
                continue
            a, sg = facet[g] >> 1, (-1 if facet[g] & 1 else 1)
            k, dr = w[a], sg * s[a]  # g faces world dr*e_k, k horizontal
            assert k != M
            w2, s2 = list(w), list(s)
            for b in range(d):
                if w[b] == k:
                    w2[b], s2[b] = M, -s[b] * dr
                elif w[b] == M:
                    w2[b], s2[b] = k, s[b] * dr
            p2 = list(pos)
            p2[k] += dr
            stack.append((g, f, w2, s2, tuple(p2)))
    return cells


def canon_polycube(cells: list[tuple[int, ...]]) -> tuple:
    m = len(cells[0])
    best = None
    for perm in itertools.permutations(range(m)):
        for signs in itertools.product((1, -1), repeat=m):
            img = [tuple(signs[j] * c[perm[j]] for j in range(m)) for c in cells]
            mn = [min(v[j] for v in img) for j in range(m)]
            key = tuple(sorted(tuple(v[j] - mn[j] for j in range(m)) for v in img))
            if best is None or key < best:
                best = key
    return best


def nets(d: int):
    V = 2 * d
    for ti, T in enumerate(nx.nonisomorphic_trees(V)):
        adj = [set(T[v]) for v in range(V)]
        seen: set[bytes] = set()
        for M in matchings(V, adj):
            g = Graph(
                V + d,
                adjacency_dict={v: [u for u in adj[v] if u > v] for v in range(V)},
                vertex_coloring=[set(range(V)), set(range(V, V + d))],
            )
            for k, (a, b) in enumerate(M):
                g.connect_vertex(V + k, [a, b])
            c = certificate(g)
            if c in seen:
                continue
            seen.add(c)
            facet = [0] * V
            for k, (a, b) in enumerate(M):
                facet[a], facet[b] = 2 * k, 2 * k + 1
            linear = max(len(x) for x in adj) <= 2
            yield ti, roll(d, adj, facet), linear


def main() -> None:
    d, out = int(sys.argv[1]), sys.argv[2]
    compare = (
        sys.argv[sys.argv.index("--compare") + 1] if "--compare" in sys.argv else None
    )
    n = nlin = 0
    canon: set[tuple] = set()
    with open(out, "w") as f:
        for ti, cells, linear in nets(d):
            assert len(set(cells)) == 2 * d, "overlap"
            f.write(
                f"{n} linear={int(linear)} cells="
                + "".join("(" + ",".join(map(str, c)) + ")" for c in cells)
                + " lattice=none\n"
            )
            n += 1
            nlin += linear
            if compare:
                canon.add(canon_polycube(cells))
    print(f"d={d} unfoldings={n} linear={nlin}", flush=True)
    if compare:
        old = set()
        for line in open(compare):
            cells = [
                tuple(map(int, c.split(",")))
                for c in re.findall(r"\(([-\d,]+)\)", line.split("lattice=")[0])
            ]
            old.add(canon_polycube(cells))
        print(
            f"  distinct polycubes={len(canon)} earlier={len(old)} identical={canon == old}"
        )


if __name__ == "__main__":
    main()
