"""Item (C): word cycle of the step-2 (3,2) rhombic phase and the burst that leads to the pentagon notch."""
from __future__ import annotations
import cmath, os, sys
from collections import Counter
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import independent_stack as s
from lineage import step_labelled, angles

def canon(labels):
    i = labels.index("Ua/+")
    return " ".join(labels[i:] + labels[:i])

def run(beta, eps, c):
    pts, b = s.initial_front(beta, eps)
    S = s.Stack(pts, b, c)
    v = angles(S)
    labels = ["Ua" if (x.imag > 0 and cmath.phase(x) > beta) else ("Ub" if x.imag > 0 else "D") for x in v]
    cyc = Counter(); tail = []
    for n in range(1, int(60 / abs(c))):
        p = S.parastichy()
        labels, gap, _ = step_labelled(S, labels)
        q = S.parastichy()
        if p == (3, 2) and q == (3, 2):
            cyc[canon(labels)] += 1
        if p[0] == 3 and (q != (3, 2) or p != (3, 2)):
            tail.append(f"{'TRP'[gap] if gap < 3 else gap}->{canon(labels) if 'Ua/+' in labels else labels}")
        if gap >= 2 or q == (3, 5):
            break
    return cyc, tail

if __name__ == "__main__":
    for beta in (0.42, 0.52):
        for r in (5.0, -5.0, 1.0):
            cyc, tail = run(beta, r * 0.001, -0.001)
            print(f"beta={beta} eps/|c|={r:+.0f}: (3,2) cycle words: " + "; ".join(f"[{w}] x{k}" for w, k in cyc.most_common()))
            print("    burst: " + " | ".join(tail[:8]), flush=True)
