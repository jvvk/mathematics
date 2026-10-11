import itertools
import networkx as nx
from networkx.generators.atlas import graph_atlas_g
from family import grow
from paths import f

found: dict[tuple[int, int], tuple] = {}
for H in graph_atlas_g()[1:]:
    if H.number_of_nodes() < 3 or not nx.is_connected(H):
        continue
    for x, y in itertools.combinations(H.nodes(), 2):
        v4 = [f(grow(H, x, y, a))[0] for a in (2, 3, 4)]
        s = v4[1] - v4[0]
        if s in (2, 4) and v4[2] - v4[1] == s and v4[0] % 2 == 1:
            key = (s, v4[0] % s if s == 4 else 1)
            if key in ((2, 1), (4, 1)) and key not in found:
                vals = [f(grow(H, x, y, a))[0] for a in range(1, 8)]
                if all(vals[i + 1] - vals[i] == s for i in range(1, 6)):
                    found[key] = (sorted(H.edges()), (x, y), vals)
                    print(key, found[key], flush=True)
print("done", list(found))
