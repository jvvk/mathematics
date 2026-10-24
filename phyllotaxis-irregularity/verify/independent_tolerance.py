"""Record independent_tolerance.out (Section 8): the event histories of independent_stack.py for two runs are the
same for overlap tolerances 1e-7, 1e-9, 1e-13 and 0. A finite reproducibility check, not a proof. Exits nonzero if
any tolerance changes a history.
Run: python3 independent_tolerance.py   (a few minutes)
"""
from __future__ import annotations
import os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from independent_stack import history


def main() -> int:
    fails = 0
    for beta, eps, c in ((0.523, 0.01, -0.002), (0.523, 0.01, -0.005)):
        seen = None
        for tol in (1e-7, 1e-9, 1e-13, 0.0):
            ev = history(beta, eps, c, max_steps=int(30 / abs(c)), tol=tol)
            line = "  ".join(f"{n}{k}{p}" for n, k, _, p in ev)
            print(f"tol={tol:g} beta={beta} eps={eps} c={c}: {line}", flush=True)
            if seen is not None and line != seen:
                print(f"FAIL history changes with tol={tol:g}"); fails += 1
            seen = line
    print("ALL CHECKS PASSED" if not fails else f"{fails} FAILURES")
    return 1 if fails else 0


if __name__ == "__main__":
    sys.exit(main())
