"""Review point 3 for Table kappa1: the O(c) loss of up mismatch through step one, kappa1 = (eps - theta)/|c|,
with every disk (seeds included) of diameter b0 + c y. Same measurement as mismatch_law.py (theta = largest
up/up mismatch at a 1,2-notch right after a step-2 triangle), only the initial front differs."""
from __future__ import annotations
import os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import independent_stack as s
from mismatch_law import notches
from seed_convention import consistent_front

def max_theta(beta: float, eps: float, c: float):
    pts, b = consistent_front(beta, eps, c)
    S = s.Stack(pts, b, c)
    prev = S.parastichy(); best = None
    for _ in range(1, int(30 / abs(c))):
        dl = S.step(); p = S.parastichy()
        if prev[0] == 3 and p[1] > prev[1]:
            for th, cu in notches(S):
                if best is None or th > best[0]:
                    best = (th, cu)
        prev = p
        if dl == -1 or p == (3, 5):
            return best
    return best

if __name__ == "__main__":
    for beta in (0.42, 0.45, 0.48, 0.50, 0.523):
        ks = []
        for c in (-0.002, -0.001, -0.0005):
            for r in (5, 8):
                eps = r * abs(c)
                th, _ = max_theta(beta, eps, c)
                ks.append((eps - th) / abs(c))
        print(f"beta={beta}: kappa1 = " + ", ".join(f"{k:.4f}" for k in ks), flush=True)
