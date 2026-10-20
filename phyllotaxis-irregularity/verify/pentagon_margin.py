"""Mechanism check (STATUS.md, item (c)).

Prediction: in the slow limit a near-equilateral triangle leaves a neighbouring 1,2-notch (down, up, up)
almost exactly ON the pentagon boundary gamma + tau = 4 pi/3 (Golé-Douady 2020, Prop. 4.3), with a safety
margin m0 = gamma + tau - 4 pi/3 that is O(|c|). Then the pentagon wins iff the next triangle is late by
more than ~ m0/|c| = O(1) visits, i.e. iff eps/|c| exceeds a constant: the ratio law.

Measure: after every step, the minimum over 1,2-notches of (gamma + tau - 4 pi/3), where tau, gamma are the
hinge angles at the two inner vertices (hinge = angle between -v_in and v_out; pi for a straight chain).
Report the minimum margin in the window starting at the first triangle of step 2, for lattice starts.
"""
from __future__ import annotations
import math, os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import independent_stack as s

def hinge(vin: complex, vout: complex) -> float:
    a = math.atan2((vout / -vin).imag, (vout / -vin).real)
    return abs(a)

def front_vectors(S) -> list[complex]:
    pts = [complex(S.disks[i][0], S.disks[i][1]) for i in S.front]
    pts.append(pts[0] + 1.0)
    return [pts[k + 1] - pts[k] for k in range(len(pts) - 1)]

def min_margin(S) -> float:
    v = front_vectors(S)
    N = len(v)
    best = math.inf
    for k in range(N):
        a, b, c = v[k], v[(k + 1) % N], v[(k + 2) % N]
        if a.imag < 0 and b.imag > 0 and c.imag > 0:  # 1,2-notch: down, up, up
            m = hinge(a, b) + hinge(b, c) - 4 * math.pi / 3
            best = min(best, m)
    return best

def run(beta: float, eps: float, c: float):
    pts, b = s.initial_front(beta, eps)
    S = s.Stack(pts, b, c)
    p = S.parastichy()
    margins = []
    phase2 = False
    for n in range(1, int(30 / abs(c))):
        dl = S.step()
        q = S.parastichy()
        if q == (3, 3) and p == (3, 2):
            phase2 = True
        if phase2:
            margins.append((n, q, dl, min_margin(S)))
        if dl == -1 or (q[1] == 5 and q[0] == 3):
            break
        p = q
    return margins

if __name__ == "__main__":
    print("lattice start (eps = 0): minimum 1,2-notch pentagon margin during step 2, vs c")
    for beta in (0.45, 0.523):
        for c in (-0.008, -0.004, -0.002, -0.001, -0.0005):
            ms = run(beta, 0.0, c)
            mm = min(m for *_, m in ms if m < math.inf) if any(m < math.inf for *_, m in ms) else float("nan")
            end = ms[-1][1] if ms else None
            print(f"  beta={beta} c={c:+.4f}: min margin = {mm:+.6f} rad, margin/|c| = {mm/abs(c):+.3f}, ended at {end}", flush=True)
    print("irregular starts, beta 0.523, c = -0.002: margin trajectory in step 2 (step, state, event, margin)")
    for eps in (0.004, 0.01):
        ms = run(0.523, eps, -0.002)
        print(f"  eps={eps} (ratio {eps/0.002:.0f}): " + "  ".join(f"{n}{q}{'TRP'[1-dl] if dl in (1,0,-1) else dl}:{m:+.4f}" for n, q, dl, m in ms[:8]))
