"""Lemma 3 (triangle step, first order) and the cushion formula, against exact geometry.

Notch A -D-> B -U-> C with hinge at B = 120 deg + delta; triangle resting on U: new disk Q tangent to B and C,
diameters d = b0 + c*y. Claims:
  X = B->Q = U e^{i pi/3} + xi,  Y = Q->C = U e^{-i pi/3} - xi,  xi = (i c / 2) e^{i beta_U} U + O(c^2);
  new hinge at B (between -D and X) = 60 deg + delta + (|c|/2) cos(beta_U - 60 deg) + O(c^2)   (c < 0).
Test: errors / c^2 bounded as c -> 0 over random notches; planted wrong formulas must blow up.
"""
from __future__ import annotations
import cmath, math, os, random, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from independent_stack import Stack

def exact(bU: float, bD: float, b: float, c: float):
    A = 0j
    dA = b + c * A.imag
    B = A + 0.0  # placeholder, rebuilt with exact tangency below
    # build A, B, C with diameters from the law (heights determine diameters, then lengths)
    B = A + b * cmath.exp(1j * bD)
    for _ in range(50):
        dB = b + c * B.imag
        B = A + (dA + dB) / 2 * cmath.exp(1j * bD)
    C = B + b * cmath.exp(1j * bU)
    for _ in range(50):
        dC = b + c * C.imag
        C = B + (dB + dC) / 2 * cmath.exp(1j * bU)
    S = Stack([], b, c)
    Q = S.apex((B.real, B.imag, dB), (C.real, C.imag, dC))
    Qz = complex(Q[0], Q[1])
    return A, B, C, Qz

def hinge(vin: complex, vout: complex) -> float:
    z = vout / -vin
    return abs(math.atan2(z.imag, z.real))

def errors(bU, bD, b, c, mut=0):
    A, B, C, Q = exact(bU, bD, b, c)
    U, D = C - B, B - A
    X, Y = Q - B, C - Q
    k = {0: 0.5, 1: -0.5, 2: 1.0}.get(mut, 0.5)
    phase = cmath.exp(1j * math.atan2(U.imag, U.real)) if mut != 3 else cmath.exp(1j * math.atan2(D.imag, D.real))
    xi = 1j * c * k * phase * U
    eX = abs(X - (U * cmath.exp(1j * math.pi / 3) + xi))
    eY = abs(Y - (U * cmath.exp(-1j * math.pi / 3) - xi))
    delta = hinge(D, U) - 2 * math.pi / 3
    beta_u = math.atan2(U.imag, U.real)
    pred = math.pi / 3 + delta + (abs(c) / 2) * math.cos(beta_u - math.pi / 3) * (1 if mut != 4 else -1)
    eH = abs(hinge(D, X) - pred)
    return eX, eY, eH

if __name__ == "__main__":
    random.seed(7)
    samples = []
    while len(samples) < 150:
        bU = random.uniform(0.05, 0.5)
        tau = math.radians(random.uniform(120.5, 135))
        bD = bU + tau - math.pi  # hinge at B = pi + bD - bU
        if bD < -1.4 or bD > -0.05:
            continue
        samples.append((bU, bD, random.uniform(0.2, 0.45)))
    bad = 0
    # A uniform bound on this sampled domain; O(c) mutants exceed it at small |c|.
    bound = 1.0
    for mut, name in ((0, "claimed formulas"), (1, "MUTANT xi sign flipped"), (2, "MUTANT xi factor 1 not 1/2"),
                      (3, "MUTANT phase beta_D not beta_U"), (4, "MUTANT cushion sign flipped")):
        worst = [0.0, 0.0, 0.0]
        accepted = True
        for bU, bD, b in samples:
            for c in (-1e-2, -1e-3, -1e-4):
                e = errors(bU, bD, b, c, mut)
                scaled = [x / c**2 for x in e]
                accepted = all(math.isfinite(x) and x < bound for x in scaled) and accepted
                worst = [max(w, x) for w, x in zip(worst, scaled)]
        print(f"{name:34s} max err/c^2:  X {worst[0]:.3g}   Y {worst[1]:.3g}   hinge {worst[2]:.3g}")
        if (mut == 0 and not accepted) or (mut != 0 and accepted):
            bad += 1
            print(f"FAIL: {name}: " + ("first-order error bound exceeded" if mut == 0 else "mutant survived"))
    print(f"{'FAIL' if bad else 'PASS'}: {len(samples)} triangle samples, error/c^2 < {bound}, 4 mutants checked, {bad} failures")
    sys.exit(1 if bad else 0)
