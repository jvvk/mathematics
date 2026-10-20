"""Hand-analysis aid for the k = 3 witnesses on Z_13 (T, 3T, 9T with no common quartet).

Questions: (1) is there a witness whose tree is also invariant under extra maps (x -> -x, ...)? (2) how many
witnesses are there, as quartet systems of T? Uses the encoder of frob.py, rooted at the fixed point 0.
"""

import argparse
import sys
import time
from itertools import combinations

from pysat.formula import IDPool
from pysat.solvers import Solver

sys.path.insert(0, __file__.rsplit("/", 1)[0])
from frob import Split, decode, encode_tree, quartet_clauses, relabel
from quartets import common_quartets


def clauses_family(n: int, k: int, sig: list[int], invs: list[list[int]], pool: IDPool):
    cls, t = encode_tree(n, 0, pool)
    qc, q = quartet_clauses(n, 0, t, pool)
    cls += qc
    inv = [0] * n
    for x, y in enumerate(sig):
        inv[y] = x

    def pw(x: int, e: int) -> int:
        for _ in range(e):
            x = inv[x]
        return x

    for Q in combinations(range(n), 4):
        a, b, c, d = Q
        for sp in (((a, b), (c, d)), ((a, c), (b, d)), ((a, d), (b, c))):
            cl = []
            for e in range(k):
                pre = tuple(tuple(pw(v, e) for v in part) for part in sp)
                Qe = tuple(sorted(v for part in pre for v in part))
                cl.append(-q[Qe, Split(frozenset(p) for p in pre)])
            cls.append(sorted(set(cl)))
    # T invariant under each tau (tau fixes the root 0): rooted triple F with outgroup F[j] maps to tau(F)
    for tau in invs:
        assert tau[0] == 0
        for F in combinations(range(1, n), 3):
            G = tuple(sorted(tau[v] for v in F))
            for j in range(3):
                cls.append([-t[F, j], t[G, G.index(tau[F[j]])]])
    return cls, t


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--n", type=int, default=13)
    ap.add_argument("--k", type=int, default=3)
    ap.add_argument("--mul", type=int, default=3)
    ap.add_argument(
        "--inv",
        type=int,
        nargs="*",
        default=[],
        help="multipliers m: T invariant under x -> m x",
    )
    ap.add_argument(
        "--enum", type=int, default=1, help="enumerate up to this many witnesses"
    )
    a = ap.parse_args()
    n = a.n
    sig = [a.mul * x % n for x in range(n)]
    invs = [[m * x % n for x in range(n)] for m in a.inv]
    pool = IDPool()
    cls, t = clauses_family(n, a.k, sig, invs, pool)
    lits = list(t.values())
    found = 0
    t0 = time.time()
    with Solver(name="cadical153", bootstrap_with=cls) as s:
        while found < a.enum and s.solve():
            m = set(l for l in s.get_model() if l > 0)
            T = decode(n, 0, t, m)
            fam = [T]
            for _ in range(a.k - 1):
                fam.append(relabel(fam[-1], sig))
            assert not common_quartets(fam)
            found += 1
            if found <= 5:
                print("T =", T, flush=True)
            s.add_clause([-v for v in lits if v in m])
        exhausted = found < a.enum
    print(
        f"n={n} mul={a.mul} inv={a.inv}: {found} witnesses{' (all)' if exhausted else '+'} in {time.time() - t0:.1f}s"
    )


if __name__ == "__main__":
    main()
