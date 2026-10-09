"""Enumerate lookahead strategies: each is a list of (depth_sum, leafmask_S, leafmask_T) ansatz terms.
Value of a strategy at y: sum 2^{c*depth_sum} * (sum of y over maskS x maskT)^a. Each is concave in y."""
from functools import lru_cache
import itertools, sys

def build(D, DT=None):
    DS = D; DT = D if DT is None else DT
    def kids(u): return (u + (0,), u + (1,))
    @lru_cache(None)
    def strat(u, v, root=False):
        out = [] if root else [((len(u) + len(v), u, v),)]
        su, sv = len(u) < DS, len(v) < DT
        if su and sv:
            (u0, u1), (v0, v1) = kids(u), kids(v)
            for A, B in ((strat(u0, v0), strat(u1, v1)), (strat(u0, v1), strat(u1, v0))):
                out += [a + b for a in A for b in B]
        if sv:
            for w in kids(v): out += list(strat(u, w))
        if su:
            for w in kids(u): out += list(strat(w, v))
        return tuple(dict.fromkeys(tuple(sorted(s)) for s in out))
    return strat((), (), True)

if __name__ == "__main__":
    for D in (1, 2):
        print(D, len(build(D)))
