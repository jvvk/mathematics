"""Critical ratio K* = eps/|c| at which the second Fibonacci step breaks (pentagon at (3,4)->(3,3)).
For fixed eps, bisect on log|c| between a breaking rate and a surviving rate; report K = eps/|c*|.
Scaling law holds if K is (nearly) independent of eps. Start: (1,2) lattice-like front, angle beta.
"""
from __future__ import annotations
import math, os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import multi_step as m

def survives(beta: float, eps: float, c: float) -> bool:
    n, base, why = m.run(beta, c, eps=eps, max_pair=8, d_min=0.005)
    return why == "reached target"

def critical_K(beta: float, eps: float, iters: int = 14) -> tuple[float, float]:
    lo, hi = eps / 1.0, eps / 12.0  # |c| values: lo survives (ratio 1), hi breaks (ratio 12)
    assert survives(beta, eps, -lo) and not survives(beta, eps, -hi), "bracket failed"
    for _ in range(iters):
        mid = math.sqrt(lo * hi)
        if survives(beta, eps, -mid):
            lo = mid
        else:
            hi = mid
    return eps / lo, eps / hi  # K bracket: survives at eps/lo, breaks at eps/hi

if __name__ == "__main__":
    for beta in (0.523, 0.50, 0.45):
        for eps in (0.002, 0.005, 0.01, 0.02):
            try:
                k1, k2 = critical_K(beta, eps)
                print(f"beta={beta} eps={eps}: K* in [{k1:.4f}, {k2:.4f}]", flush=True)
            except AssertionError as e:
                print(f"beta={beta} eps={eps}: {e}", flush=True)
