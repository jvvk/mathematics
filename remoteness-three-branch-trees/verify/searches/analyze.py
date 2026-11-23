"""Step 1: structure of ALL remoteness minimisers (ties included), to sharpen Conj 4.4.
Hypotheses tested on every D with k segments, lengths <= L:
  H1  every minimiser has <= 2 branching vertices (strong form of Conj 4.4)
  H2  in every 2-branch minimiser the internal segment has length l_1 = max D
  H3  if no starlike tree is optimal, some minimiser is a 2-branch tree with internal segment l_1
Records (D, sigma_star, sigma_double, splits of the 2-branch minimisers) for the split / threshold rules.
usage: python3 analyze.py KMIN KMAX L  -> analyze_k{KMIN}-{KMAX}_L{L}.jsonl
"""

import collections
import itertools
import json
import sys

import networkx as nx
import numpy as np

import os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from remote import assignments, leaf_forms, skeletons

kmin, kmax, L = map(int, sys.argv[1:4])
out = open(f"analyze_k{kmin}-{kmax}_L{L}.jsonl", "w")
viol = collections.Counter()
tot = 0
for k in range(max(kmin, 3), kmax + 1):
    sk = skeletons(k)
    for D in itertools.combinations_with_replacement(range(L, 0, -1), k):
        A = assignments(D).astype(float)
        base = (A * (A - 1) / 2).sum(1)
        per = []
        for idx, (E, leaves, nb) in enumerate(sk):
            mx = np.full(len(A), -np.inf)
            for c, M in leaf_forms(k, idx):
                mx = np.maximum(
                    mx, A @ c + np.einsum("pi,ij,pj->p", A, M, A) - A @ M.sum(0) + base
                )
            per.append(mx)
        m = min(float(x.min()) for x in per)
        mins = []
        for idx, mx in enumerate(per):
            E, leaves, nb = sk[idx]
            for p in np.nonzero(np.abs(mx - m) < 1e-9)[0]:
                mins.append((idx, nb, tuple(int(t) for t in A[p])))
        tot += 1
        nbs = [x[1] for x in mins]
        if max(nbs) > 2:
            viol["H1"] += 1
        splits = []
        for idx, nb, lab in mins:
            if nb != 2:
                continue
            E, leaves, _ = sk[idx]
            G = nx.Graph()
            G.add_edges_from(E)
            internal = [
                i for i, (a, b) in enumerate(E) if G.degree(a) > 1 and G.degree(b) > 1
            ]
            assert len(internal) == 1
            i0 = internal[0]
            a, b = E[i0]
            if lab[i0] != max(D):
                viol["H2"] += 1
            side = {a: [], b: []}
            for i, (u, v) in enumerate(E):
                if i == i0:
                    continue
                hub = u if u in (a, b) else v
                side[hub].append(lab[i])
            splits.append(
                (lab[i0], sorted(side[a], reverse=True), sorted(side[b], reverse=True))
            )
        star = min(float(per[i].min()) for i in range(len(sk)) if sk[i][2] == 1)
        dbl = [float(per[i].min()) for i in range(len(sk)) if sk[i][2] == 2]
        dbl = min(dbl) if dbl else None
        if min(nbs) == 2 and not any(s[0] == max(D) for s in splits):
            viol["H3"] += 1
        out.write(
            json.dumps(
                {
                    "D": D,
                    "min": m,
                    "star": star,
                    "double": dbl,
                    "nbs": sorted(set(nbs)),
                    "splits": splits,
                }
            )
            + "\n"
        )
    print(f"k={k} done, {tot} sequences, violations {dict(viol)}", flush=True)
print("TOTAL", tot, "violations", dict(viol))
