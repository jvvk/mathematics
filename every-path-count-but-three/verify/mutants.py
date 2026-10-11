"""verify.prove must REJECT each mutant."""
import networkx as nx
from verify import prove, FAMILIES

E, x, y, s, r = FAMILIES["6a+1"]
muts = {
    "wrong intercept": (E, x, y, 6, 3),
    "wrong slope": (E, x, y, 4, 1),
    "edge removed": (E[:-1], x, y, 6, 1),
    "edge added": (E + [(0, 4)], x, y, 6, 1),
    "other poles": (E, 0, 2, 6, 1),
    "4a+3 claimed 4a+1": (FAMILIES["4a+3"][0], 1, 4, 4, 1),
}
for name, (E2, a, b, s2, r2) in muts.items():
    try:
        prove(nx.Graph(E2), a, b, s2, r2)
        print("SURVIVED", name)
    except AssertionError as e:
        print("killed", name)
