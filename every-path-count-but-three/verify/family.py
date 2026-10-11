import itertools
import networkx as nx
from networkx.generators.atlas import graph_atlas_g
from paths import f


def grow(H: nx.Graph, x: int, y: int, a: int) -> nx.Graph:
    G = H.copy()
    n = max(H.nodes()) + 1
    for i in range(a):
        G.add_edge(x, n + i); G.add_edge(y, n + i)
    return G


if __name__ == "__main__":
    hits = []
    for H in graph_atlas_g()[1:200]:
        if H.number_of_nodes() < 2 or not nx.is_connected(H):
            continue
        for x, y in itertools.combinations(H.nodes(), 2):
            vals = [f(grow(H, x, y, a))[0] for a in range(1, 8)]
            d = [vals[i + 1] - vals[i] for i in range(len(vals) - 1)]
            if all(t == 2 for t in d[1:]) and vals[-1] % 2 == 1:
                hits.append((H.number_of_nodes(), H.number_of_edges(), sorted(H.edges()), (x, y), vals))
    hits.sort()
    for h in hits[:12]:
        print(h)
    print(len(hits))
