"""Exact minimum remoteness over all trees with a given segment sequence D (Allie-du Preez-Hefty-Mafunda Conj 4.4).

A D-tree = series-reduced skeleton S (no degree-2 vertex, k = |D| edges) with the lengths of D assigned to its edges.
Remoteness rho = max_v sigma(v) / (n - 1), n = 1 + sum D; the maximum of sigma over a tree is attained at a leaf
(sigma is strictly convex along paths), and leaves of the D-tree are leaves of S.
For a leaf x of S:  sigma(x) = sum_{y in V(S)} d(x, y) + sum_e [ (l_e - 1) d(x, near_x(e)) + l_e (l_e - 1) / 2 ],
d linear in the lengths. All length assignments are evaluated vectorised.
Branching vertices of the D-tree = internal vertices of S. Conjecture: some (or every) minimiser has <= 2.
"""

from __future__ import annotations

import functools
import itertools

import networkx as nx
import numpy as np


@functools.cache
def skeletons(k: int):
    """series-reduced trees with k edges (k + 1 vertices, no vertex of degree 2), as (edges, leaves, n_internal)."""
    out = []
    if k == 1:
        return [(((0, 1),), (0, 1), 0)]
    for T in nx.nonisomorphic_trees(k + 1):
        if any(d == 2 for _, d in T.degree()):
            continue
        E = tuple(T.edges())
        leaves = tuple(v for v in T if T.degree(v) == 1)
        out.append((E, leaves, sum(1 for v in T if T.degree(v) >= 3)))
    return out


@functools.cache
def leaf_forms(k: int, idx: int):
    """for each leaf x: (c_x, A_x) with sigma(x) = c_x . l + l^T A_x l - 1^T A_x l + sum l(l-1)/2."""
    E, leaves, _ = skeletons(k)[idx]
    G = nx.Graph()
    G.add_edges_from(E)
    eid = {frozenset(e): i for i, e in enumerate(E)}
    forms = []
    for x in leaves:
        paths = nx.single_source_shortest_path(G, x)

        def pe(y):
            p = paths[y]
            return [eid[frozenset((p[i], p[i + 1]))] for i in range(len(p) - 1)]

        c = np.zeros(k)
        for y in G:
            for f in pe(y):
                c[f] += 1
        A = np.zeros((k, k))
        for i, (a, b) in enumerate(E):
            near = a if len(paths[a]) < len(paths[b]) else b
            for f in pe(near):
                A[i, f] += 1
        forms.append((c, A))
    return forms


def assignments(D):
    """distinct orderings of the multiset D (rows)."""
    return np.array(sorted(set(itertools.permutations(D))), dtype=np.int64)


def remoteness_table(D):
    """list of (max-leaf-status minimum over assignments, n_branching) per skeleton."""
    k = len(D)
    L = assignments(D).astype(float)
    base = (L * (L - 1) / 2).sum(1)
    res = []
    for idx, (E, leaves, nb) in enumerate(skeletons(k)):
        best = None
        mx = np.full(len(L), -np.inf)
        for c, A in leaf_forms(k, idx):
            s = L @ c + np.einsum("pi,ij,pj->p", L, A, L) - L @ A.sum(0) + base
            mx = np.maximum(mx, s)
        i = int(np.argmin(mx))
        res.append((float(mx[i]), nb, tuple(int(t) for t in L[i]), idx))
    return res


def brute_sigma_max(E, lengths):
    """independent check: build the subdivided tree, BFS from every vertex."""
    G = nx.Graph()
    nxt = max(max(e) for e in E) + 1
    for (a, b), l in zip(E, lengths):
        prev = a
        for _ in range(l - 1):
            G.add_edge(prev, nxt)
            prev = nxt
            nxt += 1
        G.add_edge(prev, b)
    return max(sum(nx.single_source_shortest_path_length(G, v).values()) for v in G)


if __name__ == "__main__":
    rng = np.random.default_rng(0)
    # self-test: formula vs BFS on random skeletons / assignments
    bad = 0
    for _ in range(300):
        k = int(rng.integers(3, 8))
        sk = skeletons(k)
        if not sk:
            continue
        idx = int(rng.integers(len(sk)))
        E, leaves, _ = sk[idx]
        l = rng.integers(1, 7, size=k).astype(float)
        f = max(
            l @ c + l @ A @ l - A.sum(0) @ l + (l * (l - 1) / 2).sum()
            for c, A in leaf_forms(k, idx)
        )
        bad += int(round(f)) != brute_sigma_max(E, [int(t) for t in l])
    print("self-test mismatches:", bad, "of 300")
