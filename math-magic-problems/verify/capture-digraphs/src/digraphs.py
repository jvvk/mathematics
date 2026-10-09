"""2-regular digraphs on n vertices (no loops, at most one arc each way; 2-cycles allowed), up to
isomorphism, plus the three open cases of Friedman's unsolved problem 21 as read from
https://erich-friedman.github.io/mathmagic/1013.html (figures a6-2-q, -r, -s).

Hexagon labels used for the hand-read graphs: 0 top-left, 1 top-right, 2 right, 3 bottom-right,
4 bottom-left, 5 left.
"""

from __future__ import annotations

from itertools import combinations, permutations

Arcs = frozenset[tuple[int, int]]

OPEN: dict[str, list[tuple[int, int]]] = {
    "q": [
        (0, 1),
        (1, 0),
        (0, 2),
        (1, 2),
        (2, 5),
        (2, 3),
        (3, 4),
        (4, 3),
        (3, 5),
        (4, 1),
        (5, 0),
        (5, 4),
    ],
    "r": [
        (0, 1),
        (0, 5),
        (1, 2),
        (1, 5),
        (2, 0),
        (2, 3),
        (3, 4),
        (3, 1),
        (4, 3),
        (4, 0),
        (5, 2),
        (5, 4),
    ],
    "s": [
        (1, 0),
        (0, 5),
        (0, 2),
        (1, 5),
        (2, 1),
        (2, 3),
        (3, 4),
        (3, 1),
        (4, 3),
        (4, 0),
        (5, 2),
        (5, 4),
    ],
}


# Diagrams marked "none" on the answers page: f (Joe DeVincentis) and u (Mark Thompson).
# Same hexagon labels as OPEN, read from figures a6-2-f and a6-2-u.
PUBLISHED_NONE: dict[str, list[tuple[int, int]]] = {
    "f": [(1, 0), (0, 5), (5, 4), (4, 3), (3, 2), (2, 1), (5, 2), (2, 5), (0, 3), (3, 0), (1, 4), (4, 1)],
    "u": [(1, 0), (0, 5), (0, 2), (1, 5), (5, 4), (5, 3), (4, 3), (4, 0), (3, 1), (3, 2), (2, 1), (2, 4)],
}
UNSOLVED = {**PUBLISHED_NONE, **OPEN}


def canon(arcs, n: int) -> Arcs:
    return frozenset(min(tuple(sorted((p[a], p[b]) for a, b in arcs)) for p in permutations(range(n))))


def is_2_regular(arcs, n: int) -> bool:
    out = [0] * n
    inn = [0] * n
    for a, b in arcs:
        out[a] += 1
        inn[b] += 1
    return (
        all(o == 2 for o in out)
        and all(i == 2 for i in inn)
        and len(set(arcs)) == len(arcs)
    )


def all_classes(n: int) -> list[Arcs]:
    """Every 2-regular digraph on n vertices, one canonical representative per class."""
    rows = [list(combinations([j for j in range(n) if j != i], 2)) for i in range(n)]
    seen: set[Arcs] = set()

    def rec(i: int, arcs: list[tuple[int, int]], indeg: list[int]) -> None:
        if i == n:
            seen.add(canon(arcs, n))
            return
        for pair in rows[i]:
            if all(indeg[j] < 2 for j in pair):
                for j in pair:
                    indeg[j] += 1
                rec(i + 1, arcs + [(i, j) for j in pair], indeg)
                for j in pair:
                    indeg[j] -= 1

    rec(0, [], [0] * n)
    return sorted(seen, key=lambda s: sorted(s))
