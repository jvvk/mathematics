"""Review point 3: the ratio law with consistent seeds (every disk, the three seeds included, of diameter
b0 + c y). Same break criterion and simulator as break_probability.py (multi_step.step); only the initial front
differs (seed_convention.consistent_front). Usage: python break_probability_consistent.py <c> <r1,r2,...>"""
from __future__ import annotations
import os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import multi_step as m
from transition_scaling import parastichy
from seed_convention import consistent_front

def run(beta: float, c: float, eps: float, max_pair: int = 5, d_min: float = 0.005):
    pts, b0 = consistent_front(beta, eps, c)
    F = sorted([(p[0] % 1.0, p[1], p[2]) for p in pts])
    base = parastichy(F)
    cur = base
    n = 0
    while True:
        n += 1
        F, g = m.step(F, b0, c)
        if min(p[2] for p in F) < d_min:
            return n, base, "ran out"
        p = parastichy(F)
        if g >= 2:
            return n, base, "pentagon"
        if p == cur:
            continue
        small = 0 if base[0] < base[1] else 1
        grew = 0 if p[0] == cur[0] + 1 else (1 if p[1] == cur[1] + 1 else -1)
        if grew != small:
            return n, base, "wrong-side triangle"
        cur = p
        if cur[small] == base[0] + base[1]:
            base = cur
            if max(base) >= max_pair:
                return n, base, "reached target"

if __name__ == "__main__":
    c = float(sys.argv[1])
    ratios = [float(x) for x in sys.argv[2].split(",")]
    betas = [0.40 + 0.12 * k / 29 for k in range(30)]
    for r in ratios:
        res = [run(b, c, r * abs(c))[2] != "reached target" for b in betas]
        print(f"c={c:+.4f} r={r}: p={sum(res)/len(res):.2f}", flush=True)
