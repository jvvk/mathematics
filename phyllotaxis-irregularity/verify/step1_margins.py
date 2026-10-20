"""N = 1: worst pentagon margin during step 1 ((1,2) -> (2,2) -> (3,2)).
Upper-side hinge h(vin, vout) = (arg(-vin) - arg(vout)) mod 2 pi. For every 3-notch (D,U,U) or (D,D,U):
margin = tau + gamma - 4 pi/3 (pentagon needs margin <= kappa-type O(c) shift). Report min margin / |c| over
the (2,2) phase, which 3-notch attains it (lineage labels), and whether a valid pentagon site ever existed.
"""
from __future__ import annotations
import cmath, math, os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import independent_stack as s
from lineage import step_labelled, angles
from pentagon_anatomy import candidates

def h(vin, vout):
    return (cmath.phase(-vin) - cmath.phase(vout)) % (2 * math.pi)

def run(beta, eps, c):
    pts, b = s.initial_front(beta, eps)
    S = s.Stack(pts, b, c)
    v = angles(S)
    labels = ["Ua" if (x.imag > 0 and cmath.phase(x) > beta) else ("Ub" if x.imag > 0 else "D") for x in v]
    worst = (math.inf, None); pent_site = False
    for n in range(1, int(30 / abs(c))):
        p = S.parastichy()
        if p == (2, 2):
            v = angles(S); N = len(v)
            for k in range(N):
                a, bb, cc = v[k], v[(k + 1) % N], v[(k + 2) % N]
                kind = "".join("U" if x.imag > 0 else "D" for x in (a, bb, cc))
                if kind in ("DUU", "DDU"):
                    m = h(a, bb) + h(bb, cc) - 4 * math.pi / 3
                    if m < worst[0]:
                        worst = (m, (kind, labels[k], labels[(k + 1) % N], labels[(k + 2) % N]))
            if 2 in candidates(S):
                pent_site = True
        labels, gap, _ = step_labelled(S, labels)
        if S.parastichy() == (3, 2) or gap >= 2:
            return worst, pent_site, gap
    return worst, pent_site, None

if __name__ == "__main__":
    for c in (-0.002, -0.0005):
        for beta in (0.42, 0.47, 0.52):
            for r in (0.0, 2.0, 5.0, 20.0, -5.0, -20.0):
                (m, who), ps, g = run(beta, r * abs(c), c)
                print(f"c={c} beta={beta} eps/|c|={r:+5.1f}: min margin/|c| = {m/abs(c) if who else float('nan'):+8.3f} at {who}  pentagon site ever: {ps}  last gap {g}", flush=True)
