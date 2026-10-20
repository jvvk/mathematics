"""Pentagon-existence law (STATUS.md, competition step).

Claim: at step 2, a pentagon site exists at a 1,2-notch (steep down D', up U_new, up U_old) iff the up-up
mismatch theta = 180 deg - hinge(U_new, U_old) exceeds the cushion kappa = hinge(D', U_new) - 60 deg; and
theta = eps - k1 |c| + o(.) with slope exactly 1 (theta inherits the step-1 irregularity frozen by Prop 2).
Measure, right after each step-2 triangle, the maximum over 1,2-notches of theta and the cushion there;
fit theta against eps at fixed c (slope, intercept/|c|).
"""
from __future__ import annotations
import cmath, math, os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import independent_stack as s

def notches(S):
    F = S.front; N = len(F)
    pts = [complex(S.disks[i][0], S.disks[i][1]) for i in F] + [complex(S.disks[F[0]][0] + 1, S.disks[F[0]][1])]
    v = [pts[k + 1] - pts[k] for k in range(N)]
    def hinge(a, b):
        z = b / -a
        return abs(math.atan2(z.imag, z.real))
    out = []
    for k in range(N):
        a, b, c = v[k], v[(k + 1) % N], v[(k + 2) % N]
        if a.imag < 0 and b.imag > 0 and c.imag > 0:
            out.append((math.pi - hinge(b, c), hinge(a, b) - math.pi / 3))
    return out

def max_theta(beta, eps, c):
    pts, b = s.initial_front(beta, eps)
    S = s.Stack(pts, b, c)
    prev = S.parastichy(); best = None
    for n in range(1, int(30 / abs(c))):
        dl = S.step(); p = S.parastichy()
        if prev[0] == 3 and p[1] > prev[1]:  # a step-2 triangle just happened
            for th, cu in notches(S):
                if best is None or th > best[0]:
                    best = (th, cu)
        prev = p
        if dl == -1 or p == (3, 5):
            return best, ("P" if dl == -1 else "ok")
    return best, "none"

if __name__ == "__main__":
    beta = 0.523
    for c in (-0.002, -0.001, -0.0005):
        xs, ys = [], []
        print(f"c={c}: eps, ratio, theta, cushion, (theta - cushion)/|c|, outcome")
        for r in (0.5, 1.0, 1.5, 2.0, 2.5, 3.0, 4.0, 6.0, 8.0):
            eps = r * abs(c)
            (th, cu), out = max_theta(beta, eps, c)
            xs.append(eps); ys.append(th)
            print(f"  {eps:.5f} {r:4.1f} {th:+.6f} {cu:+.6f} {(th - cu)/abs(c):+.3f} {out}", flush=True)
        n = len(xs); mx = sum(xs) / n; my = sum(ys) / n
        slope = sum((x - mx) * (y - my) for x, y in zip(xs, ys)) / sum((x - mx) ** 2 for x in xs)
        icpt = my - slope * mx
        print(f"  fit theta = {slope:.4f} eps {icpt/abs(c):+.3f} |c|")
