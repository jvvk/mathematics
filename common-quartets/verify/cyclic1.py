"""Lean cyclic search: one tree T on n leaves, witness T, sT, ..., s^(k-1)T with s of order k.
s^t T displays s^t(Q-split) iff T displays it, so 'no common quartet' becomes: for every 4-set Q and split j of Q,
not all of T's splits on s^-t(Q) (t = 0..k-1) are the preimages of j."""
import argparse
import sys
import time
from itertools import combinations

from pysat.formula import IDPool
from pysat.solvers import Solver

sys.path.insert(0, __file__.rsplit("/", 1)[0])
from cyclic import index_of, split_of  # noqa: E402
from decode import build, verify  # noqa: E402
from sat_h3 import encode  # noqa: E402


def relabel(t, f):
    return f(t) if isinstance(t, int) else tuple(relabel(c, f) for c in t)


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--n", type=int, required=True)
    ap.add_argument("--k", type=int, required=True)
    ap.add_argument("--perm", required=True)
    a = ap.parse_args()
    n, k = a.n, a.k
    sig = list(range(n))
    for cyc in a.perm.split(","):
        c = [int(x) for x in cyc.split()]
        for i, v in enumerate(c):
            sig[v] = c[(i + 1) % len(c)]
    inv = [0] * n
    for v in range(n):
        inv[sig[v]] = v
    pool = IDPool()
    cls = encode(n, 1, pool)
    for Q in combinations(range(n), 4):
        for j in range(3):
            sp = split_of(Q, j)
            clause = []
            for t in range(k):
                # preimage under s^t
                pre = sp
                for _ in range(t):
                    pre = frozenset(frozenset(inv[v] for v in part) for part in pre)
                R = tuple(sorted(set().union(*pre)))
                clause.append(-pool.id(("x", 0, R, index_of(R, pre))))
            cls.append(clause)
    t0 = time.time()
    with Solver(name="cadical153", bootstrap_with=cls) as s:
        r = s.solve()
        print(f"n={n} k={k} sigma={a.perm}: {'SAT' if r else 'UNSAT'} in {time.time()-t0:.1f}s, {len(cls)} clauses", flush=True)
        if r:
            m = set(l for l in s.get_model() if l > 0)
            T = build(n, {Q: j for Q in combinations(range(n), 4) for j in range(3) if pool.id(("x", 0, Q, j)) in m})
            trees = [T]
            for _ in range(k - 1):
                trees.append(relabel(trees[-1], lambda x: sig[x]))
            print("T =", T)
            c = verify(trees)
            print("independent check on T and its images, common quartets:", c)
            assert c == 0


if __name__ == "__main__":
    main()
