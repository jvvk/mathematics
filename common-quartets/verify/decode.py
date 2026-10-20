"""Rebuild binary trees from a SAT model's quartet system and re-check them with quartets.py alone."""
import sys
from itertools import combinations

sys.path.insert(0, __file__.rsplit("/", 1)[0])
from quartets import common_quartets, quartet_map  # noqa: E402

Edge = tuple[int, int]


def build(n: int, q: dict[tuple[int, ...], int]) -> tuple:
    """Stepwise insertion: adjacency on vertices (leaves 0..n-1, internal n..), insert leaf v on the unique edge
    making every quartet with v match q."""
    adj: dict[int, set[int]] = {0: {n}, 1: {n}, 2: {n}, n: {0, 1, 2}}
    nxt = n + 1

    def to_tuple(root_leaf: int) -> tuple:
        def rec(u: int, p: int):
            ch = [w for w in adj[u] if w != p]
            return u if not ch else tuple(rec(w, u) for w in ch)
        (nb,) = adj[root_leaf]
        return (root_leaf, rec(nb, root_leaf))

    for v in range(3, n):
        edges = [(a, b) for a in adj for b in adj[a] if a < b]
        ok = []
        for a, b in edges:
            m = nxt
            adj[a].discard(b); adj[b].discard(a)
            adj[m] = {a, b, v}; adj[a].add(m); adj[b].add(m); adj[v] = {m}
            qm = quartet_map(to_tuple(0))
            if all(_idx(Q, qm[frozenset(Q)]) == q[Q] for Q in combinations(range(v + 1), 4) if v in Q):
                ok.append((a, b))
            for w in (a, b, v):
                adj[w].discard(m)
            del adj[m], adj[v]
            adj[a].add(b); adj[b].add(a)
        assert len(ok) == 1, (v, ok)
        a, b = ok[0]
        adj[a].discard(b); adj[b].discard(a)
        adj[nxt] = {a, b, v}; adj[a].add(nxt); adj[b].add(nxt); adj[v] = {nxt}
        nxt += 1
    return to_tuple(0)


def _idx(Q, sp) -> int:
    a = Q[0]
    partner = next(next(iter(p - {a})) for p in sp if a in p)
    return Q.index(partner) - 1


def verify(trees: list[tuple]) -> int:
    return len(common_quartets(trees))
