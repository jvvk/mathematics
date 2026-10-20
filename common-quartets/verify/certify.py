"""LRAT certificates for the n = 14 by-shape instances: write DIMACS, CaDiCaL 2.1.3 --lrat, check with lrat-check
(drat-trim repo), log, delete the proof. Exit status 20 = UNSAT from CaDiCaL."""
import argparse
import json
import os
import subprocess
import sys
import time
from itertools import combinations

from pysat.formula import CNF, IDPool

sys.path.insert(0, __file__.rsplit("/", 1)[0])
from quartets import quartet_map  # noqa: E402
from sat_h3 import encode, split_index  # noqa: E402
from shapes import unrooted  # noqa: E402

CADICAL = os.environ.get("CADICAL", os.path.expanduser("~/.local/src/cadical/build/cadical"))
LRATCHECK = os.environ.get("LRATCHECK", os.path.expanduser("~/.local/src/drat-trim/lrat-check"))


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--n", type=int, default=14)
    ap.add_argument("--start", type=int, default=0)
    ap.add_argument("--stop", type=int, default=10**9)
    ap.add_argument("--tmp", required=True)
    ap.add_argument("--log", required=True)
    a = ap.parse_args()
    n = a.n
    pool = IDPool()
    base = encode(n, 3, pool)
    shapes = unrooted(n)
    for i, t in enumerate(shapes[a.start:a.stop], start=a.start):
        qm = quartet_map(t)
        units = [[pool.id(("x", 0, Q, split_index(Q, qm[frozenset(Q)])))] for Q in combinations(range(n), 4)]
        cnf, proof = f"{a.tmp}/s{i}.cnf", f"{a.tmp}/s{i}.lrat"
        CNF(from_clauses=base + units).to_file(cnf)
        t0 = time.time()
        r = subprocess.run([CADICAL, "-q", "--lrat=1", "--binary=0", cnf, proof])
        t1 = time.time()
        c = subprocess.run([LRATCHECK, cnf, proof], capture_output=True, text=True)
        ok = r.returncode == 20 and "c VERIFIED" in c.stdout
        rec = dict(n=n, shape=i, solver_exit=r.returncode, check="VERIFIED" if ok else "FAIL",
                   solve_s=round(t1 - t0, 1), check_s=round(time.time() - t1, 1),
                   proof_mb=round(os.path.getsize(proof) / 2**20, 1))
        os.remove(proof); os.remove(cnf)
        print(json.dumps(rec), flush=True)
        with open(a.log, "a") as f:
            f.write(json.dumps(rec) + "\n")
        if not ok:
            print(c.stdout[-2000:], c.stderr[-2000:])
            sys.exit(1)


if __name__ == "__main__":
    main()
