"""Search for a witness of the form T, sigma(T), sigma^2(T) with sigma of order 3 (or other orders via --cycles)."""
import argparse
import sys
import time
from itertools import combinations

from pysat.formula import IDPool
from pysat.solvers import Solver

sys.path.insert(0, __file__.rsplit("/", 1)[0])
from decode import build, verify  # noqa: E402
from sat_h3 import encode  # noqa: E402

SPLITS = [((0, 1), (2, 3)), ((0, 2), (1, 3)), ((0, 3), (1, 2))]


def split_of(Q: tuple[int, ...], j: int) -> frozenset:
    (p, q), (r, s) = SPLITS[j]
    return frozenset([frozenset([Q[p], Q[q]]), frozenset([Q[r], Q[s]])])


def index_of(Q: tuple[int, ...], sp: frozenset) -> int:
    return next(j for j in range(3) if split_of(Q, j) == sp)


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--n", type=int, default=13)
    ap.add_argument("--k", type=int, default=3)
    ap.add_argument("--perm", required=True, help="cycle notation like '0 1 2,3 4 5' (unlisted points fixed)")
    a = ap.parse_args()
    n = a.n
    sig = list(range(n))
    for cyc in a.perm.split(","):
        c = [int(x) for x in cyc.split()]
        for i, v in enumerate(c):
            sig[v] = c[(i + 1) % len(c)]
    pool = IDPool()
    cls = encode(n, a.k, pool)
    for t in range(a.k - 1):
        for Q in combinations(range(n), 4):
            R = tuple(sorted(sig[v] for v in Q))
            for j in range(3):
                img = frozenset(frozenset(sig[v] for v in part) for part in split_of(Q, j))
                jj = index_of(R, img)
                x, y = pool.id(("x", t, Q, j)), pool.id(("x", t + 1, R, jj))
                cls += [[-x, y], [x, -y]]
    t0 = time.time()
    with Solver(name="cadical153", bootstrap_with=cls) as s:
        r = s.solve()
        print(f"n={n} sigma={a.perm}: {'SAT' if r else 'UNSAT'} in {time.time()-t0:.1f}s", flush=True)
        if r:
            m = set(l for l in s.get_model() if l > 0)
            trees = [build(n, {Q: j for Q in combinations(range(n), 4) for j in range(3) if pool.id(("x", t, Q, j)) in m}) for t in range(a.k)]
            for t, tr in enumerate(trees):
                print(f"T{t+1} =", tr)
            print("independent check, common quartets:", verify(trees))


if __name__ == "__main__":
    main()
