"""Check the first-order rhombic-transition formula against exact geometry.

Claim: for a notch A -D-> B -U-> C (D down, U up) with diameters d = b0 + c*y, the new disk Q
tangent to A and C gives X = A->Q, Y = Q->C with
    X = U * (1 + i c e^{i beta_D}) + O(c^2),   Y = D * (1 - i c e^{i beta_U}) + O(c^2),
equivalently xi = X - U = i c U D / b. Test: error / c^2 stays bounded as c -> 0.
"""
from __future__ import annotations
import cmath, math, random
import os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from tracking_irregularity import place

def check(bU: float, bD: float, b: float, c: float) -> tuple[float, float]:
    # place B at height y0 so all three old disks have diameters from the law d = b0 + c*y
    A = 0j
    B = A + b * cmath.exp(1j * bD)
    C = B + b * cmath.exp(1j * bU)
    b0 = b  # law d(y) = b0 + c*y; old disks use their own heights (exact model, not the b approx)
    dA, dB, dC = b0 + c * A.imag, b0 + c * B.imag, b0 + c * C.imag
    # rebuild so tangencies are exact for these diameters: keep directions, fix lengths
    B = A + (dA + dB) / 2 * cmath.exp(1j * bD)
    C = B + (dB + dC) / 2 * cmath.exp(1j * bU)
    Q = place((A.real, A.imag, dA), (C.real, C.imag, dC), b0, c)
    Qz = complex(Q[0], Q[1])
    U, D = C - B, B - A
    X, Y = Qz - A, C - Qz
    Xp = U * (1 + 1j * c * cmath.exp(1j * math.atan2(D.imag, D.real)))
    Yp = D * (1 - 1j * c * cmath.exp(1j * math.atan2(U.imag, U.real)))
    return abs(X - Xp), abs(Y - Yp)

if __name__ == "__main__":
    random.seed(1)
    worst = 0.0
    for _ in range(200):
        bU = random.uniform(0.1, 1.2)
        bD = random.uniform(-1.2, -0.1)
        tau = math.pi - (bU - bD)  # hinge at B; rhombic iff tau in [pi/3, 2pi/3]
        if not (math.pi / 3 < tau < 2 * math.pi / 3):
            continue
        b = random.uniform(0.2, 0.5)
        for c in (-1e-2, -1e-3, -1e-4):
            ex, ey = check(bU, bD, b, c)
            worst = max(worst, ex / c**2, ey / c**2)
    print(f"max over samples of error/c^2 = {worst:.4f}  (bounded => formula is exact to first order)")
