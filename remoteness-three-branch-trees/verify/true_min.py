"""True minimiser of remoteness over ALL D-trees for a given D (exhaustive: every skeleton x every distinct assignment).
Uses remote.py (skeletons, leaf_forms, assignments), the machinery verified 300/300 against BFS earlier.
usage: python3 true_min.py l1 l2 ... lk"""
import os, sys
import numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from remote import skeletons, assignments, leaf_forms

D = tuple(sorted(map(int, sys.argv[1:]), reverse=True)); k = len(D)
A = assignments(D).astype(np.int64); base = (A * (A - 1) // 2).sum(1)
sk = skeletons(k); print("k", k, "skeletons", len(sk), "assignments", len(A), flush=True)
res = []
for idx, (E, leaves, nb) in enumerate(sk):
    mx = np.full(len(A), -1, dtype=np.int64)
    for c, M in leaf_forms(k, idx):
        c = np.asarray(c, dtype=np.int64); M = np.asarray(M, dtype=np.int64)
        v = A @ c + np.einsum("pi,ij,pj->p", A, M, A) - A @ M.sum(0) + base
        mx = np.maximum(mx, v)
    p = int(np.argmin(mx)); res.append((int(mx[p]), nb, idx, tuple(int(t) for t in A[p]), E))
res.sort()
for r in res[:6]: print("max transmission", r[0], "branch vertices", r[1], "skeleton", r[2], "lengths", r[3], "edges", r[4])
by_nb = {}
for r in res: by_nb[r[1]] = min(by_nb.get(r[1], 10**18), r[0])
print("best by number of branch vertices:", dict(sorted(by_nb.items())))

# Regression check: the recorded table for the note's sequence (Proposition 3.3, as maximum transmission).
EXPECT = {(53, 23, 21, 9, 9, 9, 1, 1, 1, 1, 1, 1): {1: 6160, 2: 5971, 3: 5962, 4: 5975, 5: 6003}}
if D in EXPECT:
    got = dict(sorted(by_nb.items()))
    if got != EXPECT[D]:
        print("CHECK FAILED: expected", EXPECT[D], "got", got); sys.exit(1)
    print("CHECK PASSED")
