"""Local pentagon-existence boundary with shrinking disks (item 6 after the 70/70 reduction).

Isolated 1,2-notch P0 -D'-> P1 -U1-> P2 -U2-> P3, diameters d = b0 + c*y at each centre. Angles: D' at beta_D,
U1 at beta_1 = beta_D + 120 deg - cushion, U2 at beta_1 + theta (so hinge(D',U1) = 60 + cushion,
hinge(U1,U2) = 180 - theta). Pentagon site: disk tangent to P0 and P3 (own diameter from its height), not
overlapping P1, P2. At c = 0 (Golé-Douady 2020 Prop 4.3) it exists iff theta >= cushion.
Measure the boundary theta*(cushion, c) by bisection and report kappa2 = (theta* - cushion)/|c|.
"""
from __future__ import annotations
import cmath, math, os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from independent_stack import Stack

def chain(beta_D, beta_1, beta_2, b0, c):
    pts = [0j]; ds = [b0]
    for ang in (beta_D, beta_1, beta_2):
        P = pts[-1]; dP = ds[-1]
        Q = P + b0 * cmath.exp(1j * ang)
        for _ in range(60):
            dQ = b0 + c * Q.imag
            Q = P + (dP + dQ) / 2 * cmath.exp(1j * ang)
        pts.append(Q); ds.append(b0 + c * Q.imag)
    return pts, ds

def exists(beta_D, cushion, theta, b0, c, tol=1e-12):
    b1 = beta_D + 2 * math.pi / 3 - cushion
    pts, ds = chain(beta_D, b1, b1 + theta, b0, c)
    S = Stack([], b0, c)
    Q = S.apex((pts[0].real, pts[0].imag, ds[0]), (pts[3].real, pts[3].imag, ds[3]))
    if Q is None:
        return False
    for k in (1, 2):
        if abs(complex(Q[0], Q[1]) - pts[k]) < (Q[2] + ds[k]) / 2 - tol:
            return False
    return True

def boundary(beta_D, cushion, b0, c):
    lo, hi = cushion - 0.05, cushion + 0.05  # theta: lo -> no site, hi -> site
    assert not exists(beta_D, cushion, lo, b0, c) and exists(beta_D, cushion, hi, b0, c)
    for _ in range(60):
        mid = (lo + hi) / 2
        if exists(beta_D, cushion, mid, b0, c):
            hi = mid
        else:
            lo = mid
    return hi

if __name__ == "__main__":
    beta_D = math.radians(-83.5)
    b0 = 0.06  # ~ disk diameter at step 2 in the runs (front of 5-7 disks on circumference 1)
    print("c = 0 check (expect theta* = cushion):")
    for cu in (0.0, 0.002, -0.002):
        print(f"  cushion {cu:+.4f}: theta* - cushion = {boundary(beta_D, cu, b0, 0.0) - cu:+.2e}")
    for b0_ in (0.06, 0.1):
        print(f"b0 = {b0_}: kappa2 = (theta* - cushion)/|c|")
        for c in (-0.004, -0.002, -0.001, -0.0005, -0.00025):
            ks = [(boundary(beta_D, cu * abs(c), b0_, c) - cu * abs(c)) / abs(c) for cu in (0.0, 0.3, 0.6)]
            print(f"  c={c:+.5f}: " + "  ".join(f"cushion {cu}|c| -> {k:.4f}" for cu, k in zip((0.0, 0.3, 0.6), ks)))
