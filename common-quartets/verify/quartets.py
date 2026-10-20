"""Quartet topologies of unrooted binary trees given as nested tuples (an unrooted tree is written
as a rooted tuple; the root position is irrelevant for splits)."""
from itertools import combinations
from typing import Iterable

Tree = tuple | int


def leaves(t: Tree) -> frozenset[int]:
    return frozenset([t]) if isinstance(t, int) else frozenset().union(*(leaves(c) for c in t))


def splits(t: Tree) -> list[frozenset[int]]:
    """One side of every edge split (clusters of the rooted writing)."""
    out: list[frozenset[int]] = []
    def rec(s: Tree) -> frozenset[int]:
        if isinstance(s, int):
            return frozenset([s])
        L = frozenset().union(*(rec(c) for c in s))
        out.append(L)
        return L
    rec(t)
    return out


def quartet_map(t: Tree) -> dict[frozenset[int], frozenset[frozenset[int]]]:
    """For each 4-set, its split {{a,b},{c,d}}. Checks the tree is binary (every 4-set resolved)."""
    X = leaves(t)
    S = splits(t)
    q = {}
    for Q in combinations(sorted(X), 4):
        Qs = frozenset(Q)
        res = set()
        for s in S:
            A = Qs & s
            if len(A) == 2:
                res.add(frozenset([A, Qs - A]))
        assert len(res) == 1, (t, Q, res)
        q[Qs] = res.pop()
    return q


def common_quartets(trees: Iterable[Tree]) -> list:
    maps = [quartet_map(t) for t in trees]
    assert len({frozenset(m) for m in maps}) == 1, "leaf sets differ"
    return [Q for Q in maps[0] if all(m[Q] == maps[0][Q] for m in maps)]
