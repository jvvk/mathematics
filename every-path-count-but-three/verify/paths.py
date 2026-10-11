"""Count simple paths between all vertex pairs; f(G) = max over pairs (u != v)."""
from collections import defaultdict
import networkx as nx


def pair_counts(G: nx.Graph) -> dict[tuple[int, int], int]:
    nodes = list(G.nodes())
    idx = {v: i for i, v in enumerate(nodes)}
    adj = [[idx[w] for w in G[v]] for v in nodes]
    cnt: dict[tuple[int, int], int] = defaultdict(int)
    for s in range(len(nodes)):
        stack = [(s, 1 << s)]
        while stack:
            v, mask = stack.pop()
            for w in adj[v]:
                if not mask >> w & 1:
                    if w > s:
                        cnt[(s, w)] += 1
                    stack.append((w, mask | 1 << w))
    return {(nodes[a], nodes[b]): c for (a, b), c in cnt.items()}


def f(G: nx.Graph) -> tuple[int, list[tuple[int, int]]]:
    pc = pair_counts(G)
    m = max(pc.values(), default=0)
    return m, [p for p, c in pc.items() if c == m]
