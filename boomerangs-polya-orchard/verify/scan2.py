"""Pruned search for B(r): only arc radii that can beat the current record are examined.

Reach <= 2a, so a >= record / 2. For each a on a grid fine enough that the blocked theta
intervals move by much less than their width, test whether the discs nearer than the
record already close every direction; only survivors get the exact treatment.
"""
from __future__ import annotations

import math
import sys
import time

import numpy as np

from orchard import _gaps, _intervals, exact_reach, lattice, polish, reach_for_radius


def scan(r: float, start: float, amax: float, dcap: float, fine: float = 0.25,
         budget: float = 110.0) -> tuple[float, float, float, bool]:
    pts, rho = lattice(dcap)
    best, best_a, best_t = start, 0.0, 0.0
    a = start / 2
    t0 = time.time()
    done = True
    while a < amax:
        if time.time() - t0 > budget:
            done = False
            break
        n = int(np.searchsorted(rho, min(best, 2 * a + r), side="right"))
        lo, w = _intervals(a, r, pts, rho, n)
        if _gaps(lo, w) or 2 * a + r < best:
            if 2 * a > best:
                D, t = reach_for_radius(a, r, pts, rho)
                if D > best:
                    best, best_a, best_t = D, a, t
        # theta-interval of a tree at distance D moves by ~ D da / (2 a^2) per da
        a += fine * (r / best) * 2 * a * a / best
    if best_a:
        best, best_a, best_t = polish(best_a, best_t, r, pts, iters=1500)
    return best, best_a, best_t, done


if __name__ == "__main__":
    inv, start, amax = float(sys.argv[1]), float(sys.argv[2]), float(sys.argv[3])
    budget = float(sys.argv[4]) if len(sys.argv) > 4 else 110.0
    r = 1 / inv
    t0 = time.time()
    D, a, th, done = scan(r, start, amax, dcap=2 * amax + 2, budget=budget)
    import json
    with open("results.jsonl", "a") as fh:
        fh.write(json.dumps({"inv_r": inv, "reach": D, "a": a, "theta": th, "complete": done}) + "\n")
    print(f"1/r={inv:5.1f}  B>={D:9.4f}  a={a:9.4f}  theta={th:.6f}  B*r^2={D*r*r:.4f}  "
          f"B*r/ln(1/r)={D*r/math.log(inv):.3f}  complete={done}  ({time.time()-t0:.0f}s)")
