"""Review point 3: the seeds of F(beta, eps) have equal diameters b0, which violates d = b0 + c y by O(|c|).
Re-run the runs of Table 1 with consistent seeds (each seed of diameter b0 + c y, consecutive seeds touching,
same bearings) and compare the event sequences with the equal-seed runs of independent_stack.py."""
from __future__ import annotations
import math, os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from independent_stack import Stack

def consistent_front(beta: float, eps: float, c: float):
    """Seeds of diameter 1 + c y (height 0 at the first seed), consecutive seeds touching: the side from
    height y0 in direction a has length L = (1 + c y0) / (1 - c sin(a)/2). The up bearings are those of
    F(beta, eps); the down bearing is solved (Newton) so that the chain closes at height 0."""
    ua, ub = beta + eps / 2, beta - eps / 2
    angs = [-math.asin(math.sin(ua) + math.sin(ub)), ua, ub]
    for _ in range(100):
        ys, Ls = [0.0], []
        for a in angs:
            L = (1 + c * ys[-1]) / (1 - c * math.sin(a) / 2)
            Ls.append(L)
            ys.append(ys[-1] + L * math.sin(a))
        if abs(ys[-1]) < 1e-15:
            break
        angs[0] -= ys[-1] / (Ls[0] * math.cos(angs[0]))
    pts, x, y = [], 0.0, 0.0
    for k, a in enumerate(angs):
        pts.append((x, y, 1 + c * y))
        x += Ls[k] * math.cos(a)
        y += Ls[k] * math.sin(a)
    lam = x
    return [(px / lam, py / lam, d / lam) for px, py, d in pts], 1 / lam


def history(pts, b0, c, max_steps):
    S = Stack(pts, b0, c)
    ev, cur = [], S.parastichy()
    for n in range(1, max_steps + 1):
        dl = S.step()
        p = S.parastichy()
        if dl != 0 or p != cur:
            kind = {1: "T", 0: "R", -1: "P"}.get(dl, f"X{dl}")
            ev.append(f"{n}{kind}{p}")
            cur = p
            if kind not in ("T", "R") or (max(p) >= 8 and min(p) >= 5):
                break
    return ev

if __name__ == "__main__":
    for beta, eps, c in ((0.523, 0.005, -0.002), (0.523, 0.005, -0.001), (0.523, 0.01, -0.005), (0.523, 0.01, -0.002)):
        pts, b0 = consistent_front(beta, eps, c)
        print(f"beta={beta} eps={eps} c={c} ratio={eps/abs(c):.1f} consistent seeds: " + " ".join(history(pts, b0, c, int(30 / abs(c)))), flush=True)
