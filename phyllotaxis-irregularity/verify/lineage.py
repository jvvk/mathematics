"""Lineage of front vectors through step 1 and step 2, to identify the pentagon notch's vectors.

Labels: initial (1,2) front edges 'D', 'Ua' (angle beta + eps/2), 'Ub' (beta - eps/2).
Rhombus on notch L1 (down) L2 (up): the new edges carry L2 then L1 (swap).
Triangle on edge L: new edges 'L/+' (L rotated +60) then 'L/-' (L rotated -60).
"""
from __future__ import annotations
import cmath, math, os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import independent_stack as s

def step_labelled(S, labels):
    F = S.front; N = len(F)
    best = None
    for a in range(N):
        for gap in range(0, N - 1):
            bidx = (a + gap + 1) % N
            P = S.disks[F[a]]; R = S.disks[F[bidx]]
            if bidx <= a:
                R = (R[0] + 1.0, R[1], R[2])
            if R[0] <= P[0]:
                continue
            Q = S.apex(P, R)
            if Q is None or (best is not None and Q[1] >= best[0][1]):
                continue
            if S.free(Q, {F[a], F[bidx]}):
                best = (Q, a, gap)
    Q, a, gap = best
    S.disks.append((Q[0] % 1.0, Q[1], Q[2])); q = len(S.disks) - 1
    # labels[k] = label of edge F[k] -> F[k+1]; rebuild as a cyclic list starting at F[a]
    rot = F[a:] + F[:a]; lab = labels[a:] + labels[:a]
    if gap == 0:
        newF = [rot[0], q] + rot[1:]; newL = [lab[0] + "/+", lab[0] + "/-"] + lab[1:]
    elif gap == 1:
        newF = [rot[0], q] + rot[2:]; newL = [lab[1], lab[0]] + lab[2:]
    else:
        newF = [rot[0], q] + rot[gap + 1:]; newL = ["P(" + ",".join(lab[:gap + 1]) + ")/+", "P/-"] + lab[gap + 1:]
    # re-sort cyclically by x while keeping edge labels attached to their left disk
    pairs = sorted(zip(newF, newL), key=lambda t: S.disks[t[0]][0])
    S.front = [p[0] for p in pairs]
    return [p[1] for p in pairs], gap, a

def angles(S):
    F = S.front; N = len(F)
    pts = [complex(S.disks[i][0], S.disks[i][1]) for i in F] + [complex(S.disks[F[0]][0] + 1, S.disks[F[0]][1])]
    return [pts[k + 1] - pts[k] for k in range(N)]

def run(beta, eps, c, verbose=True):
    pts, b = s.initial_front(beta, eps)
    S = s.Stack(pts, b, c)
    v = angles(S)
    labels = ["Ua" if (x.imag > 0 and cmath.phase(x) > beta) else ("Ub" if x.imag > 0 else "D") for x in v]
    prev = S.parastichy(); out = []
    for n in range(1, int(30 / abs(c))):
        labels, gap, a = step_labelled(S, labels)
        p = S.parastichy()
        if gap != 1 and verbose:
            v = angles(S)
            desc = "  ".join(f"{l}:{math.degrees(cmath.phase(x)):.3f}" for l, x in zip(labels, v))
            print(f"  step {n} {'TRP'[gap] if gap < 3 else gap} {prev}->{p}  front: {desc}")
        prev = p
        if gap >= 2 or p == (3, 5):
            break
    return S, labels

if __name__ == "__main__":
    for eps in (0.01, -0.01):
        print(f"beta 0.523, c -0.002, eps {eps}")
        run(0.523, eps, -0.002)
