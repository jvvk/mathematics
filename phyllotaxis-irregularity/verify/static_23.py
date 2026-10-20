"""Near-regular front with 2 downs and 3 ups (word D D U1 U2 U3), notch hinge h(D, U1) = 60 deg + sigma,
up bearings u1, u1 + eps, u1 + eps/2 (so the 1,2-notch D, U1, U2 has up/up hinge 180 - eps), equal downs.
Max relative deviation of ups and downs is O(eps). Question: is the first new disk a pentagon when
eps > sigma? Independent simulator, unit-length vectors scaled to circumference 1, all seeds equal size."""
from __future__ import annotations
import math, os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from independent_stack import Stack

def front(sigma_deg, eps):
    sig = math.radians(sigma_deg)
    def closure(u1):
        bd = u1 - 2 * math.pi / 3 + sig
        return 2 * math.sin(bd) + math.sin(u1) + math.sin(u1 + eps) + math.sin(u1 + eps / 2), bd
    lo, hi = 0.3, 1.2
    for _ in range(200):
        mid = (lo + hi) / 2
        if (closure(lo)[0] > 0) == (closure(mid)[0] > 0): lo = mid
        else: hi = mid
    u1 = (lo + hi) / 2
    bd = closure(u1)[1]
    angs = [bd, bd, u1, u1 + eps, u1 + eps / 2]
    L = sum(math.cos(a) for a in angs)
    b = 1 / L
    pts = [(0.0, 0.0, b)]
    for a in angs[:-1]:
        x, y, _ = pts[-1]
        pts.append((x + b * math.cos(a), y + b * math.sin(a), b))
    us = [complex(math.cos(a), math.sin(a)) for a in angs[2:]]
    m = sum(us) / 3
    etaU = max(abs(u - m) for u in us) / abs(m)
    return pts, b, math.degrees(u1), math.degrees(bd), etaU

if __name__ == "__main__":
    for eps in (0.02, 0.005, 0.001):
        for frac in (0.5, 0.9, 1.1, 2.0):
            sigma = math.degrees(eps) * frac
            pts, b, u1, bd, etaU = front(sigma, eps)
            for c in (0.0, -1e-6, -1e-4):
                S = Stack(pts, b, c)
                p0 = S.parastichy()
                ev = None
                for n in range(1, 60):
                    dl = S.step()
                    if dl != 0:
                        ev = (n, {1: "T", -1: "P"}.get(dl, dl), p0, S.parastichy()); break
                print(f"eps={eps} sigma/eps={frac} u1={u1:.2f} bd={bd:.2f} etaU={etaU:.4f} c={c:g}: first non-R {ev}")
