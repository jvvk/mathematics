"""Decide 'three binary trees on n leaves with no common quartet' by fixing T1 to each unlabelled shape.

Complete: any triple can be relabelled so that T1 is the chosen representative of its shape.
"""
import argparse
import json
import sys
import time
from itertools import combinations

from pysat.formula import IDPool
from pysat.solvers import Solver

sys.path.insert(0, __file__.rsplit("/", 1)[0])
from quartets import quartet_map  # noqa: E402
from sat_h3 import encode, split_index  # noqa: E402
from shapes import unrooted  # noqa: E402


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--n", type=int, required=True)
    ap.add_argument("--start", type=int, default=0)
    ap.add_argument("--stop", type=int, default=10**9)
    ap.add_argument("--log", default=None)
    a = ap.parse_args()
    n = a.n
    pool = IDPool()
    base = encode(n, 3, pool)
    shapes = unrooted(n)
    log = open(a.log, "a") if a.log else None
    for i, t in enumerate(shapes[a.start:a.stop], start=a.start):
        qm = quartet_map(t)
        units = [[pool.id(("x", 0, Q, split_index(Q, qm[frozenset(Q)])))] for Q in combinations(range(n), 4)]
        t0 = time.time()
        with Solver(name="cadical153", bootstrap_with=base + units) as s:
            r = s.solve()
        rec = dict(n=n, shape=i, of=len(shapes), result="SAT" if r else "UNSAT", secs=round(time.time() - t0, 2), T1=repr(t))
        print(json.dumps(rec), flush=True)
        if log:
            log.write(json.dumps(rec) + "\n"); log.flush()


if __name__ == "__main__":
    main()
