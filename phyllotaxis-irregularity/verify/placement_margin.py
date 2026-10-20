"""Placement margin: when the pentagon site Q is placed, how much lower is it than the next candidate, and
did any disk placed while Q waited come close to Q? Units: current disk diameter d_Q.
"""
from __future__ import annotations
import math, os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import independent_stack as s
from pentagon_anatomy import candidates

def all_candidates(S):
    F = S.front; N = len(F); out = []
    for a in range(N):
        for gap in range(0, min(3, N - 1)):
            bidx = (a + gap + 1) % N
            P = S.disks[F[a]]; R = S.disks[F[bidx]]
            if bidx <= a:
                R = (R[0] + 1.0, R[1], R[2])
            if R[0] <= P[0]:
                continue
            Q = S.apex(P, R)
            if Q is None or not S.free(Q, {F[a], F[bidx]}):
                continue
            out.append((Q[1], gap, Q))
    return sorted(out)

def run(beta, eps, c):
    pts, b = s.initial_front(beta, eps)
    S = s.Stack(pts, b, c)
    Qsite = None; closest = math.inf
    for n in range(1, int(30 / abs(c))):
        p = S.parastichy()
        if p[0] == 3 and p[1] >= 3:
            cs = all_candidates(S)
            pent = [x for x in cs if x[1] == 2]
            if pent and Qsite is None:
                Qsite = pent[0][2]
            if Qsite is not None and cs[0][1] == 2:
                gap_next = (cs[1][0] - cs[0][0]) / Qsite[2] if len(cs) > 1 else math.inf
                return gap_next, closest
        nd = len(S.disks)
        dl = S.step()
        if Qsite is not None and dl != -1:
            x, y, d = S.disks[-1]
            dist = min(math.hypot(x + sh - Qsite[0], y - Qsite[1]) for sh in (-1, 0, 1)) / ((d + Qsite[2]) / 2)
            closest = min(closest, dist)
        if dl == -1 or S.parastichy() == (3, 5):
            return None, closest

if __name__ == "__main__":
    gaps = []; clos = []
    for c in (-0.002, -0.001, -0.0005):
        for r in (3.2, 4.0, 6.0, 10.0):
            for k in range(6):
                beta = 0.40 + 0.12 * k / 5
                g, cl = run(beta, r * abs(c), c)
                if g is not None:
                    gaps.append(g); clos.append(cl)
        print(f"c={c}: n={len(gaps)}  gap to next candidate / d: min {min(gaps):.3f} max {max(gaps):.3f};"
              f"  closest approach of a waiting-time disk to Q (in tangency units): min {min(clos):.3f}", flush=True)
