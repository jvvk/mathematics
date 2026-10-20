"""Unlabelled unrooted binary trees on n leaves (one labelled representative each, leaves 0..n-1)."""
from functools import lru_cache

import networkx as nx


@lru_cache(None)
def rooted(m: int) -> tuple:
    """Rooted binary shapes on m leaves as nested tuples of 'L'."""
    if m == 1:
        return ("L",)
    out = []
    for a in range(1, m // 2 + 1):
        for i, s in enumerate(rooted(a)):
            for j, t in enumerate(rooted(m - a)):
                if a == m - a and j < i:
                    continue
                out.append((s, t))
    return tuple(out)


def _graph(t) -> nx.Graph:
    g = nx.Graph()
    c = [0]
    def rec(s) -> int:
        v = c[0]; c[0] += 1
        g.add_node(v)
        if s != "L":
            for ch in s:
                g.add_edge(v, rec(ch))
        return v
    root = rec(t)
    leaf = c[0]
    g.add_edge(root, leaf)
    return g


def unrooted(n: int) -> list[tuple]:
    reps: list[nx.Graph] = []
    seen: dict[str, list[nx.Graph]] = {}
    for t in rooted(n - 1):
        g = _graph(t)
        key = nx.weisfeiler_lehman_graph_hash(g)
        if any(nx.is_isomorphic(g, h) for h in seen.get(key, [])):
            continue
        seen.setdefault(key, []).append(g)
        reps.append(g)
    return [_label(g) for g in reps]


def _label(g: nx.Graph) -> tuple:
    leaves = [v for v in g if g.degree(v) == 1]
    lab = {v: i for i, v in enumerate(leaves)}
    r = leaves[0]
    (nb,) = g[r]
    def rec(u, p):
        ch = [w for w in g[u] if w != p]
        return lab[u] if not ch else tuple(rec(w, u) for w in ch)
    return (lab[r], rec(nb, r))


if __name__ == "__main__":
    for n in range(4, 15):
        print(n, len(unrooted(n)))
