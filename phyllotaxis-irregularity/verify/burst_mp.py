"""Item (C): step-2 burst in the regime |c| << |eps| << 1, computed at c = 0 in 60-digit arithmetic.

For each of the six words of the (3,2) cycle, build the front at the moment its first notch reaches
120 deg + eta (burst_certify.at_threshold: lineage offsets +-eps/2 frozen by Prop 2, closure exact), rescale to
circumference 1, and run constant-diameter stacking (mp_stack = 60-digit port of independent_stack, lineage
labels from lineage.step_labelled). At every step report the event and the decision margin: the height gap
between the chosen site and the next valid site, in units of eps * d. A margin of order eps * d (not eta)
means the decision survives the O(c) per-step terms when |c| << |eps|.
"""
from __future__ import annotations
import os, sys
from mpmath import mp, mpf, cos, sin
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
mp.dps = 60
import mp_stack as ms
from burst_certify import at_threshold
from lineage import step_labelled

def valid_heights(S):
    F = S.front; N = len(F); ys = []
    for a in range(N):
        for gap in range(0, N - 1):
            bidx = (a + gap + 1) % N
            P = S.disks[F[a]]; R = S.disks[F[bidx]]
            if bidx <= a:
                R = (R[0] + 1, R[1], R[2])
            if R[0] <= P[0]:
                continue
            Q = S.apex(P, R)
            if Q is not None and S.free(Q, {F[a], F[bidx]}):
                ys.append(Q[1])
    return sorted(ys)

def run(word, eps, eta, max_events=6):
    ang = at_threshold(word, eps, eta)
    L = sum(cos(t) for t in ang)
    b = 1 / L
    pts = [(mpf(0), mpf(0), b)]
    for t in ang[:-1]:
        x, y, _ = pts[-1]
        pts.append((x + b * cos(t), y + b * sin(t), b))
    S = ms.Stack(pts, b, mpf(0), tol=mpf("1e-45"))
    # labels: edge k from front[k] to front[k+1]; Stack sorts the front by x, initial x increasing already
    labels = list(word)
    events = []
    for _ in range(max_events):
        ys = valid_heights(S)
        margin = (ys[1] - ys[0]) / (eps * b) if len(ys) > 1 else mpf("inf")
        labels, gap, _a = step_labelled(S, labels)
        ev = "TRP"[gap] if gap < 3 else f"G{gap}"
        events.append((ev, margin, list(labels)))
        if gap >= 2:
            break
    return events

if __name__ == "__main__":
    cycle = ["Ua/+ Ua/- Ub/+ D Ub/-", "Ua/+ Ub/- Ua/- Ub/+ D", "Ua/+ Ub/- Ub/+ Ua/- D",
             "Ua/+ D Ub/- Ub/+ Ua/-", "Ua/+ D Ub/+ Ub/- Ua/-", "Ua/+ Ua/- D Ub/+ Ub/-"]
    for eps in (mpf("1e-5"), mpf("1e-7")):
        print(f"eps = {mp.nstr(eps, 2)}, eta = 1e-6 eps")
        for w in cycle:
            ev = run(w.split(), eps, eps * mpf("1e-6"))
            seq = " ".join(e for e, _, _ in ev)
            ms_ = " ".join(mp.nstr(m, 4) for _, m, _ in ev)
            pent = [l for l in ev[-1][2] if l.startswith("P(")]
            print(f"  [{w}]: {seq}   margins/(eps d): {ms_}   {pent[0].split(')')[0] + ')' if pent else ''}", flush=True)
