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

def check(bU: float, bD: float, b: float, c: float, mut=0) -> tuple[float, float]:
    A = 0j
    b0 = b
    # Exact recurrence: L = (d + d_next)/2, d_next = d + c*L*sin(beta).
    dA = b0 + c * A.imag
    LD = dA / (1 - c * math.sin(bD) / 2)
    B = A + LD * cmath.exp(1j * bD)
    dB = dA + c * LD * math.sin(bD)
    LU = dB / (1 - c * math.sin(bU) / 2)
    C = B + LU * cmath.exp(1j * bU)
    dC = dB + c * LU * math.sin(bU)
    Q = place((A.real, A.imag, dA), (C.real, C.imag, dC), b0, c)
    Qz = complex(Q[0], Q[1])
    disks = ((A, dA), (B, dB), (C, dC), (Qz, Q[2]))
    residuals = [abs(d - (b0 + c * z.imag)) for z, d in disks]
    residuals += [abs(abs(disks[i][0] - disks[j][0]) - (disks[i][1] + disks[j][1]) / 2)
                  for i, j in ((0, 1), (1, 2), (0, 3), (2, 3))]
    if not all(math.isfinite(r) and r < 1e-12 for r in residuals):
        print(f"FAIL: tangency/diameter-law residuals {residuals} for bU,bD,b,c={bU,bD,b,c}")
        print("FAIL: rhombic geometry verification failed")
        sys.exit(1)
    U, D = C - B, B - A
    X, Y = Qz - A, C - Qz
    k = {0: 1, 1: -1, 2: 0.5}[mut]
    Xp = U * (1 + k * 1j * c * cmath.exp(1j * math.atan2(D.imag, D.real)))
    Yp = D * (1 - k * 1j * c * cmath.exp(1j * math.atan2(U.imag, U.real)))
    return abs(X - Xp), abs(Y - Yp)

if __name__ == "__main__":
    random.seed(1)
    samples = [(0.4, -0.8, 0.3)]  # referee's diameter-law regression case
    for _ in range(200):
        bU = random.uniform(0.1, 1.2)
        bD = random.uniform(-1.2, -0.1)
        tau = math.pi - (bU - bD)  # hinge at B; rhombic iff tau in [pi/3, 2pi/3]
        if not (math.pi / 3 < tau < 2 * math.pi / 3):
            continue
        samples.append((bU, bD, random.uniform(0.2, 0.5)))
    bad = 0
    # A uniform bound on this sampled domain; O(c) mutants exceed it at small |c|.
    bound = 1.0
    for mut, name in ((0, "claimed formulas"), (1, "MUTANT first-order sign flipped"),
                      (2, "MUTANT coefficient 1/2 not 1")):
        worst, accepted = 0.0, True
        for bU, bD, b in samples:
            for c in (-1e-2, -1e-3, -1e-4):
                e = check(bU, bD, b, c, mut)
                scaled = [x / c**2 for x in e]
                accepted = all(math.isfinite(x) and x < bound for x in scaled) and accepted
                worst = max(worst, *scaled)
        print(f"{name:34s} max error/c^2 = {worst:.4f}, bound {bound}: "
              + ("accepted" if accepted else "rejected"))
        if (mut == 0 and not accepted) or (mut != 0 and accepted):
            bad += 1
            print(f"FAIL: {name}: " + ("first-order error bound exceeded" if mut == 0 else "mutant survived"))
    print(f"{'FAIL' if bad else 'PASS'}: {len(samples)} rhombic samples, tangency/diameter-law residuals < 1e-12, 2 mutants checked, {bad} failures")
    sys.exit(1 if bad else 0)
