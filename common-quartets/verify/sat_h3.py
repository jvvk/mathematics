"""SAT encoding: k binary trees on n leaves with no common quartet split.

A full quartet system (one split per 4-set) is the quartet set of a binary tree iff its restriction to every 5-set
is the quartet set of one of the 15 binary 5-leaf trees (Colonius-Schulze 1981; Bandelt-Dress 1986). count_trees()
re-checks that on small n against (2n-5)!!.
"""
import argparse
import sys
import time
from itertools import combinations, permutations

from pysat.card import CardEnc, EncType
from pysat.formula import IDPool
from pysat.solvers import Solver

sys.path.insert(0, __file__.rsplit("/", 1)[0])
from quartets import quartet_map  # noqa: E402


def split_index(Q: tuple[int, ...], sp: frozenset) -> int:
    """Splits of sorted Q=(a,b,c,d): 0: ab|cd, 1: ac|bd, 2: ad|bc."""
    a = Q[0]
    partner = next(next(iter(p - {a})) for p in sp if a in p)
    return Q.index(partner) - 1


def five_leaf_patterns() -> list[tuple[int, ...]]:
    """The 15 quartet patterns of binary trees on leaves 0..4, ordered by combinations(range(5), 4)."""
    pats = set()
    for p in permutations(range(5)):
        t = ((p[0], p[1]), p[2], (p[3], p[4]))
        qm = quartet_map(t)
        pats.add(tuple(split_index(Q, qm[frozenset(Q)]) for Q in combinations(range(5), 4)))
    assert len(pats) == 15
    return sorted(pats)


PATS = five_leaf_patterns()


def encode(n: int, k: int, pool: IDPool) -> list[list[int]]:
    cls: list[list[int]] = []
    quads = list(combinations(range(n), 4))
    x = {(t, Q, j): pool.id(("x", t, Q, j)) for t in range(k) for Q in quads for j in range(3)}
    for t in range(k):
        for Q in quads:
            lits = [x[t, Q, j] for j in range(3)]
            cls += CardEnc.equals(lits, 1, vpool=pool, encoding=EncType.pairwise).clauses
        for F in combinations(range(n), 5):
            ys = []
            for pi, pat in enumerate(PATS):
                y = pool.id(("y", t, F, pi))
                ys.append(y)
                for qi, Qloc in enumerate(combinations(range(5), 4)):
                    Q = tuple(F[i] for i in Qloc)
                    cls.append([-y, x[t, Q, pat[qi]]])
            cls.append(ys)
    if k > 1:
        for Q in quads:
            for j in range(3):
                cls.append([-x[t, Q, j] for t in range(k)])
    return cls


def count_trees(n: int) -> int:
    pool = IDPool()
    cls = encode(n, 1, pool)
    xs = [pool.id(("x", 0, Q, j)) for Q in combinations(range(n), 4) for j in range(3)]
    c = 0
    with Solver(name="cadical153", bootstrap_with=cls) as s:
        while s.solve():
            m = set(l for l in s.get_model() if l > 0)
            c += 1
            s.add_clause([-v for v in xs if v in m])
    return c


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--count", type=int, nargs="*", default=[])
    ap.add_argument("--n", type=int)
    ap.add_argument("--k", type=int, default=3)
    a = ap.parse_args()
    df = {5: 15, 6: 105, 7: 945}
    for n in a.count:
        c = count_trees(n)
        print(f"n={n}: {c} trees (expected {df[n]})", flush=True)
        assert c == df[n]
    if a.n:
        pool = IDPool()
        cls = encode(a.n, a.k, pool)
        t0 = time.time()
        with Solver(name="cadical153", bootstrap_with=cls) as s:
            r = s.solve()
            print(f"n={a.n} k={a.k}: {'SAT' if r else 'UNSAT'} in {time.time()-t0:.1f}s, {len(cls)} clauses", flush=True)
            if r:
                m = set(l for l in s.get_model() if l > 0)
                from decode import build, verify
                trees = []
                for t in range(a.k):
                    q = {Q: j for Q in combinations(range(a.n), 4) for j in range(3) if pool.id(("x", t, Q, j)) in m}
                    trees.append(build(a.n, q))
                    print(f"T{t+1} =", trees[-1])
                c = verify(trees)
                print("independent check, common quartets:", c)
                assert c == 0


if __name__ == "__main__":
    main()
