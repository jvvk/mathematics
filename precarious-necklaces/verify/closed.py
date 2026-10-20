"""Closed form a_{k-s}(k) = s P_{floor(s/2)+1} + (k-s) P_{ceil(s/2)}: compare with M and test constructions."""
from __future__ import annotations
import math, itertools, sys
from ext import j_precarious
from framework import M
PR = [2, 3, 5, 7, 11, 13]
P = lambda t: math.prod(PR[:t])
def formula(k, s): return s * P(s // 2 + 1) + (k - s) * P((s + 1) // 2)

LET = "ABCDEFGHIJKLMNOP"
def construct(k, s):
    """s odd: h+1 pair rhythms + (k-2h-2) fixed colours per block. s even: h pairs, cluster of k-s colours
    before each group of p_{h+1} blocks."""
    if s % 2:
        m = s // 2 + 1
        pairs = [(LET[2*i], LET[2*i+1], PR[i]) for i in range(m)]
        fixed = LET[2*m:k]
        nb = P(m)
        return "".join("".join(a+b if j % p == 0 else b+a for a, b, p in pairs) + fixed for j in range(nb))
    h = s // 2
    pairs = [(LET[2*i], LET[2*i+1], PR[i]) for i in range(h)]
    cluster = LET[2*h:k]
    q = PR[h]
    blk = lambda j: "".join(a+b if j % p == 0 else b+a for a, b, p in pairs)
    return "".join(cluster + "".join(blk(g*q+t) for t in range(q)) for g in range(P(h)))

cases = [(3,1),(3,2),(4,1),(4,2),(4,3),(5,2),(5,3),(5,4),(6,2),(6,3),(6,4),(6,5),(7,4),(7,5),(7,6)]
for k, s in cases:
    w = construct(k, s)
    ok = j_precarious(w, k - s) and len(set(w)) == k
    print(f"k={k} s={s}: formula {formula(k,s)}, construction length {len(w)}, valid {ok}", flush=True)
# compare formula with the exhaustive optimisation where cheap
for k, s, pr in [(4,2,(2,3,5)),(4,3,(2,3,5)),(5,2,(2,3,5)),(5,3,(2,3,5)),(5,4,(2,3,5,7))]:
    print(f"M({k},s={s}) = {M(k, k-s, pr)[0]} vs formula {formula(k,s)}", flush=True)
