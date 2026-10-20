"""N = 1, item (2): which cyclic arrangements (lineage words) does the (2,2) phase visit?
Dangerous: 'D' immediately followed by 'Ua' then 'Ub/+' (degenerate DUU triple). Reachable combinatorially in
three passes; the claim is that the stacking order (lowest notch first) never visits it.
"""
from __future__ import annotations
import cmath, os, sys
from collections import Counter
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import independent_stack as s
from lineage import step_labelled, angles

def canon(labels):
    i = labels.index("Ua") if "Ua" in labels else 0
    return " ".join(labels[i:] + labels[:i])

def run(beta, eps, c):
    pts, b = s.initial_front(beta, eps)
    S = s.Stack(pts, b, c)
    v = angles(S)
    labels = ["Ua" if (x.imag > 0 and cmath.phase(x) > beta) else ("Ub" if x.imag > 0 else "D") for x in v]
    seen = Counter(); dangerous = 0; steps = 0
    for n in range(1, int(60 / abs(c))):
        if S.parastichy() == (2, 2):
            w = canon(labels); seen[w] += 1; steps += 1
            L = labels; N = len(L)
            if any(L[k] == "D" and L[(k + 1) % N] == "Ua" and L[(k + 2) % N] == "Ub/+" for k in range(N)):
                dangerous += 1
        labels, gap, _ = step_labelled(S, labels)
        if S.parastichy() == (3, 2) or gap >= 2:
            break
    return seen, dangerous, steps

if __name__ == "__main__":
    for beta in (0.42, 0.52):
        for r in (20.0, 100.0, -100.0):
            seen, dang, steps = run(beta, r * 0.001, -0.001)
            print(f"beta={beta} eps/|c|={r:+.0f}: (2,2) steps {steps}, dangerous visits {dang}, words: "
                  + "; ".join(f"[{w}] x{k}" for w, k in seen.most_common()), flush=True)
