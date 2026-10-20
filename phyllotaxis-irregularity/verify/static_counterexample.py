"""Static first-step pentagon: F(beta, eps) with the flatter up vector first (eps < 0 in initial_front's
labelling) and notch excess sigma = tau - 60 deg smaller than the mismatch |eps|. Independent simulator.
Reports sigma, |eps|, the first non-rhombic event, and the max relative deviation of the up vectors."""
from __future__ import annotations
import math, os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from independent_stack import Stack, initial_front

def notch(beta, eps):
    ua, ub = beta + eps / 2, beta - eps / 2
    bd = -math.asin(math.sin(ua) + math.sin(ub))
    return math.degrees(bd + math.pi - ua) - 60.0  # tau - 60 for the notch (D, Ua); Ua follows D

def first_events(beta, eps, c, steps=40):
    pts, b = initial_front(beta, eps)
    S = Stack(pts, b, c)
    out = []
    for n in range(1, steps + 1):
        before = S.parastichy()
        dl = S.step()
        k = {1: "T", 0: "R", -1: "P"}.get(dl, f"X{dl}")
        if k != "R":
            out.append((n, k, before, S.parastichy()))
            break
    return out

if __name__ == "__main__":
    for eps in (-0.02, -0.005):
        for beta in (0.5233, 0.5234, 0.5235, 0.5236):
            s = notch(beta, eps)
            for c in (0.0, -1e-5, -1e-3):
                ev = first_events(beta, eps, c)
                etaU = abs(math.sin(eps / 4)) * 1.0  # |Ua - mean| / |mean| for two unit vectors at +-eps/2
                print(f"eps={eps:+.3f} beta={beta} sigma={s:+.4f} deg |eps|={math.degrees(abs(eps)):.4f} deg "
                      f"etaU={etaU:.4f} c={c:g}: {ev}")
