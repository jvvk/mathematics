import itertools
import networkx as nx
from networkx.generators.atlas import graph_atlas_g
from family import grow
from paths import f

res: dict[tuple[int, int], tuple] = {}
for H in graph_atlas_g()[1:200]:
    if H.number_of_nodes() < 2 or not nx.is_connected(H):
        continue
    for x, y in itertools.combinations(H.nodes(), 2):
        vals = [f(grow(H, x, y, a))[0] for a in range(1, 8)]
        d = [vals[i + 1] - vals[i] for i in range(len(vals) - 1)]
        if len(set(d[2:])) == 1 and all(v % 2 for v in vals[2:]):
            s = d[-1]
            key = (s, vals[-1] % s if s else vals[-1])
            cand = (H.number_of_nodes(), H.number_of_edges(), sorted(H.edges()), (x, y), vals)
            if key not in res or cand < res[key]:
                res[key] = cand
for k in sorted(res):
    print(k, res[k])
