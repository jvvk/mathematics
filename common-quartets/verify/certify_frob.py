"""LRAT certificate for an unsatisfiable symmetric instance of frob.py (e.g. --n 40 --k 4 --perm mul:3):
write DIMACS, solve with CaDiCaL 2.1.3 --lrat, check with lrat-check, log the result, delete the proof."""

import argparse
import json
import os
import subprocess
import sys
import time

from pysat.formula import CNF, IDPool

sys.path.insert(0, __file__.rsplit("/", 1)[0])
from certify import CADICAL, LRATCHECK
from frob import build, parse_perm


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--n", type=int, required=True)
    ap.add_argument("--k", type=int, required=True)
    ap.add_argument("--perm", required=True)
    ap.add_argument("--root", type=int, default=0)
    ap.add_argument(
        "--tmp", required=True, help="scratch directory for the CNF and proof"
    )
    ap.add_argument(
        "--log", default=os.path.join(os.path.dirname(__file__), "frob_lrat.jsonl")
    )
    a = ap.parse_args()
    pool = IDPool()
    cls, _ = build(a.n, a.k, parse_perm(a.n, a.perm), a.root, pool)
    cnf, proof = f"{a.tmp}/frob_{a.n}_{a.k}.cnf", f"{a.tmp}/frob_{a.n}_{a.k}.lrat"
    CNF(from_clauses=cls).to_file(cnf)
    t0 = time.time()
    r = subprocess.run([CADICAL, "-q", "--lrat=1", "--binary=0", cnf, proof])
    t1 = time.time()
    c = subprocess.run([LRATCHECK, cnf, proof], capture_output=True, text=True)
    ok = r.returncode == 20 and "c VERIFIED" in c.stdout
    rec = dict(
        n=a.n,
        k=a.k,
        perm=a.perm,
        solver_exit=r.returncode,
        check="VERIFIED" if ok else "FAIL",
        solve_s=round(t1 - t0, 1),
        check_s=round(time.time() - t1, 1),
        proof_mb=round(os.path.getsize(proof) / 2**20, 1),
    )
    os.remove(proof)
    os.remove(cnf)
    print(json.dumps(rec), flush=True)
    with open(a.log, "a") as f:
        f.write(json.dumps(rec) + "\n")
    if not ok:
        print(c.stdout[-2000:], c.stderr[-2000:])
        sys.exit(1)


if __name__ == "__main__":
    main()
