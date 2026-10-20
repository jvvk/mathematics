"""Anatomy of the step-2 pentagon: front geometry and candidate heights around the event.
For each step in a window, print the front (vector angles in degrees, U/D), the hinge at each vertex, and the
lowest candidate of each type (T: gap 0, R: gap 1, P: gap 2) with its parents, so the competition is visible.
"""
from __future__ import annotations
import cmath, math, os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import independent_stack as s

def candidates(S):
    F = S.front; N = len(F); out = {}
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
            if gap not in out or Q[1] < out[gap][0]:
                out[gap] = (Q[1], a)
    return out

def describe(S):
    F = S.front; N = len(F)
    pts = [complex(S.disks[i][0], S.disks[i][1]) for i in F] + [complex(S.disks[F[0]][0] + 1, S.disks[F[0]][1])]
    v = [pts[k + 1] - pts[k] for k in range(N)]
    lab = "".join("U" if x.imag > 0 else "D" for x in v)
    ang = [round(math.degrees(cmath.phase(x)), 2) for x in v]
    hinges = []
    for k in range(N):
        vin, vout = v[k - 1], v[k]
        z = vout / -vin
        hinges.append(round(math.degrees(abs(math.atan2(z.imag, z.real))), 2))
    return lab, ang, hinges

def run(beta, eps, c, window=6):
    pts, b = s.initial_front(beta, eps)
    S = s.Stack(pts, b, c)
    log = []
    prev = S.parastichy()
    for n in range(1, int(30 / abs(c))):
        lab, ang, hin = describe(S)
        cand = candidates(S)
        dl = S.step()
        p = S.parastichy()
        log.append((n, prev, p, dl, lab, ang, hin, cand))
        prev = p
        if dl == -1 or p == (3, 5):
            break
    # print the window ending at the event, starting a few steps before the (3,2)->(3,3) triangle
    k0 = max(i for i, e in enumerate(log) if e[1] == (3, 2) and e[2] == (3, 3)) - 2
    for n, p0, p1, dl, lab, ang, hin, cand in log[k0:]:
        ev = {1: "T", 0: "R", -1: "P"}[dl]
        cs = "  ".join(f"{'TRP'[g]}:y={y:.5f}@{a}" for g, (y, a) in sorted(cand.items()))
        print(f"  step {n} {p0}->{p1} {ev}  front {lab}  angles {ang}  hinges {hin}\n      candidates {cs}")

if __name__ == "__main__":
    for eps, tag in ((0.01, "BREAKS (ratio 5)"), (0.004, "SURVIVES (ratio 2)")):
        print(f"beta 0.523, c -0.002, eps {eps}: {tag}")
        run(0.523, eps, -0.002)
