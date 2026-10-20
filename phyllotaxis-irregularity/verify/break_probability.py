"""K*: break probability p(r) of the second Fibonacci step versus r = eps/|c|.

For each ratio r and rate c, run (1,2) starts over a fine grid of starting angles beta (a proxy for the
uncontrolled phase of the discrete dynamics) and record the fraction whose step (3,2)->(3,5) is broken
(pentagon or wrong-side triangle). Sharp constant: p jumps 0 -> 1 at one r, independent of c.
Band: p rises over [K_lo, K_hi]; report the edges and the 50% point, and whether they converge as c -> 0.
"""
from __future__ import annotations
import os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import multi_step as m

def broken(beta: float, eps: float, c: float) -> bool:
    n, base, why = m.run(beta, c, eps=eps, max_pair=5, d_min=0.005)
    return why != "reached target"

if __name__ == "__main__":
    betas = [0.40 + 0.12 * k / 29 for k in range(30)]  # 0.40 .. 0.52
    ratios = [1.5, 2.0, 2.5, 3.0, 3.5, 4.0, 4.5, 5.0, 6.0]
    for c in (-0.002, -0.001, -0.0005):
        row = []
        for r in ratios:
            p = sum(broken(b, r * abs(c), c) for b in betas) / len(betas)
            row.append(p)
        print(f"c={c:+.4f}  " + "  ".join(f"r={r}:{p:.2f}" for r, p in zip(ratios, row)), flush=True)
