"""Item 6 reduction test: does every valid pentagon site that appears during step 2 get placed?

For each run, during step 2 (front has 3 downs and >= 3 ups), check every step for a valid (non-overlapping)
pentagon candidate. Record: site ever existed (E), pentagon placed (P), steps from first existence to placement.
If E <=> P in every run, placement reduces to local existence at one notch.
"""
from __future__ import annotations
import os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import independent_stack as s
from pentagon_anatomy import candidates

def run(beta, eps, c):
    pts, b = s.initial_front(beta, eps)
    S = s.Stack(pts, b, c)
    first_exist = None
    for n in range(1, int(30 / abs(c))):
        p = S.parastichy()
        if p[0] == 3 and p[1] >= 3 and first_exist is None:
            if 2 in candidates(S):
                first_exist = n
        dl = S.step()
        q = S.parastichy()
        if dl == -1:
            return first_exist, n
        if q == (3, 5):
            return first_exist, None
    return first_exist, None

if __name__ == "__main__":
    c = -0.001
    betas = [0.40 + 0.12 * k / 9 for k in range(10)]
    agree = disagree = 0
    lags = []
    for r in (2.0, 2.5, 2.8, 3.0, 3.2, 3.5, 4.0):
        row = []
        for beta in betas:
            e, pl = run(beta, r * abs(c), c)
            E, P = e is not None, pl is not None
            agree += (E == P); disagree += (E != P)
            if E and P:
                lags.append(pl - e)
            row.append("PE" if (E and P) else ("E!" if E else ("P!" if P else "..")))
        print(f"r={r}: " + " ".join(row), flush=True)
    print(f"runs where existence == placement: {agree}; disagreements: {disagree}; "
          f"steps from first existence to placement: min {min(lags) if lags else '-'}, max {max(lags) if lags else '-'}")
