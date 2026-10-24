"""The two simulators (multi_step.step, independent_stack.Stack) give the same events, disk for disk, from the
fronts of Table 1 with every disk of diameter b0 + c y (seed_convention.consistent_front)."""
from __future__ import annotations
import os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import multi_step as m
from transition_scaling import parastichy
from seed_convention import consistent_front, history

def history_ms(pts, b0, c, max_steps):
    F = sorted([(p[0] % 1.0, p[1], p[2]) for p in pts])
    ev, cur = [], parastichy(F)
    for n in range(1, max_steps + 1):
        F, g = m.step(F, b0, c)
        p = parastichy(F)
        if g != 1 or p != cur:
            kind = {0: "T", 1: "R", 2: "P"}.get(g, f"X{g}")
            if kind != "R" or p != cur:
                ev.append(f"{n}{kind}{p}")
            cur = p
            if kind not in ("T", "R") or (max(p) >= 8 and min(p) >= 5):
                break
    return ev

if __name__ == "__main__":
    bad = 0
    for beta, eps, c in ((0.523, 0.005, -0.0025), (0.523, 0.005, -0.00125), (0.523, 0.01, -0.005), (0.523, 0.01, -0.0025)):
        pts, b0 = consistent_front(beta, eps, c)
        a = history(pts, b0, c, int(30 / abs(c)))
        b = history_ms(pts, b0, c, int(30 / abs(c)))
        print(f"eps={eps} c={c}: {'SAME' if a == b else 'DIFFERENT'}\n  independent: {' '.join(a)}\n  multi_step:  {' '.join(b)}", flush=True)
        if a != b:
            bad += 1
            print(f"FAIL: simulator histories disagree for eps={eps}, c={c}")
    print(f"{'FAIL' if bad else 'PASS'}: 4 simulator comparisons, {bad} disagreements")
    sys.exit(1 if bad else 0)
