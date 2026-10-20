"""Independent recount for Proposition 5.3: trees T on Z_13 with T, 3T, 9T sharing no quartet.

Uses the three-tree five-point encoding of sat_h3.py (quartet variables per tree, 5-subset consistency) with the
second and third trees tied to the images of the first, as in cyclic.py; shares no encoding code with frob.py.
Every model is blocked on the first tree's quartet variables until none remain. Expected: 19440.
"""

import sys
import time
from itertools import combinations

from pysat.formula import IDPool
from pysat.solvers import Solver

sys.path.insert(0, __file__.rsplit("/", 1)[0])
from cyclic import index_of, split_of
from sat_h3 import encode

N = 13


def main() -> None:
    sig = [3 * x % N for x in range(N)]
    pool = IDPool()
    cls = encode(N, 3, pool)
    for t in range(2):
        for Q in combinations(range(N), 4):
            R = tuple(sorted(sig[v] for v in Q))
            for j in range(3):
                img = frozenset(
                    frozenset(sig[v] for v in part) for part in split_of(Q, j)
                )
                x, y = (
                    pool.id(("x", t, Q, j)),
                    pool.id(("x", t + 1, R, index_of(R, img))),
                )
                cls += [[-x, y], [x, -y]]
    first = [
        pool.id(("x", 0, Q, j)) for Q in combinations(range(N), 4) for j in range(3)
    ]
    count = 0
    t0 = time.time()
    with Solver(name="cadical153", bootstrap_with=cls) as s:
        while s.solve():
            m = set(l for l in s.get_model() if l > 0)
            s.add_clause([-v for v in first if v in m])
            count += 1
    print(
        f"{count} trees T on Z_13 with T, 3T, 9T sharing no quartet ({time.time() - t0:.0f} s)"
    )
    assert count == 19440


if __name__ == "__main__":
    main()
