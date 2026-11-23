"""Independent recheck of Proposition 3.3 (shares no code with true_min.py / remote.py).
Skeletons: networkx nonisomorphic trees on k+1 vertices with no vertex of degree 2.
Value of a length assignment: max over leaves x of F(x) = sum_e l_e * dist(x, nearer end of e), with dist computed
from explicit weighted path lengths (all-pairs on the skeleton for each assignment is too slow, so we precompute, for
each leaf x and edge e, the list of edges on the path from x to the nearer end of e; F is then a sum of products).
usage: python3 recheck_table.py l1 ... lk   -> prints min C by number of branch vertices."""
import itertools, sys
from collections import defaultdict
import networkx as nx
import numpy as np

D = sorted(map(int, sys.argv[1:]), reverse=True); k = len(D); N = sum(D)
skels = [T for T in nx.nonisomorphic_trees(k + 1) if all(d != 2 for _, d in T.degree())]
perms = np.array(sorted(set(itertools.permutations(D))), dtype=np.int64)
print("k", k, "series-reduced skeletons", len(skels), "distinct assignments", len(perms), flush=True)
best = defaultdict(lambda: None)
for T in skels:
    E = list(T.edges()); idx = {frozenset(e): i for i, e in enumerate(E)}
    leaves = [v for v in T if T.degree(v) == 1]; hb = sum(1 for v in T if T.degree(v) >= 3)
    vals = []
    for x in leaves:
        # coefficient matrix W[e][f] = 1 if edge f lies on the path from x to the nearer end of edge e
        W = np.zeros((k, k), dtype=np.int64)
        for e in E:
            pu = nx.shortest_path(T, x, e[0]); pv = nx.shortest_path(T, x, e[1])
            p = pu if len(pu) < len(pv) else pv
            for a, b in zip(p, p[1:]): W[idx[frozenset((a, b))], idx[frozenset(e)]] += 1  # row f, col e
        vals.append(np.einsum("pf,fe,pe->p", perms, W, perms))
    C = np.max(np.stack(vals), axis=0).min()
    best[hb] = C if best[hb] is None else min(best[hb], C)
print("min C by branch vertices:", {h: int(best[h]) for h in sorted(best)})

# Regression check: Proposition 3.3 (values of C) for the note's sequence.
EXPECT = {(53, 23, 21, 9, 9, 9, 1, 1, 1, 1, 1, 1): {1: 4081, 2: 3892, 3: 3883, 4: 3896, 5: 3924}}
if tuple(D) in EXPECT:
    got = {h: int(best[h]) for h in sorted(best)}
    if got != EXPECT[tuple(D)]:
        print("CHECK FAILED: expected", EXPECT[tuple(D)], "got", got); sys.exit(1)
    print("CHECK PASSED")
