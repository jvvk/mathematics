"""Deterministic check of the two-circle lemma: for disjoint circles (P,a), (Q,1), the line through
A = P + a*uA and B = Q + uB has normalised offsets (XA, XB) with density 1/(pi^2 sqrt(1-x^2) sqrt(1-y^2)).
Sum over the four preimages of 1/(4 pi^2 |Jacobian|), Jacobian by central differences.
Also checks the chord identity  sum |AB| = 4 m'.(Q-P).  Mutant: overlapping circles must FAIL."""
import numpy as np, sys
def offsets(tA, tB, a, D):
    uA = np.array([np.cos(tA), np.sin(tA)]); uB = np.array([np.cos(tB), np.sin(tB)])
    A = np.array([-D, 0.0]) + a * uA; B = uB; d = B - A
    m = np.array([-d[1], d[0]]) / np.hypot(*d); m = m if m[1] > 0 else -m
    return np.array([m @ uA, m @ uB])
def density(x, y, a, D, h=1e-6, strict=True):
    c = (a * x - y) / D
    if abs(c) >= 1: return None
    phi = np.arccos(c); m = np.array([np.cos(phi), np.sin(phi)]); mp = np.array([-m[1], m[0]])
    tot, chords = 0.0, 0.0
    for sA in (1, -1):
        for sB in (1, -1):
            uA = x * m + sA * np.sqrt(1 - x * x) * mp; uB = y * m + sB * np.sqrt(1 - y * y) * mp
            tA, tB = np.arctan2(uA[1], uA[0]), np.arctan2(uB[1], uB[0])
            if strict: assert np.allclose(offsets(tA, tB, a, D), [x, y], atol=1e-9)
            J = np.column_stack([(offsets(tA + h, tB, a, D) - offsets(tA - h, tB, a, D)) / (2 * h),
                                 (offsets(tA, tB + h, a, D) - offsets(tA, tB - h, a, D)) / (2 * h)])
            tot += 1 / (4 * np.pi**2 * abs(np.linalg.det(J)))
            A = np.array([-D, 0.0]) + a * uA; chords += abs(mp @ (uB - A))
    return tot, chords, abs(mp @ np.array([D, 0.0]))
def run(cases, strict=True):
    rng = np.random.default_rng(1); worst_d = worst_c = 0.0
    for a, D in cases:
        for _ in range(200):
            x, y = rng.uniform(-0.97, 0.97, 2)
            res = density(x, y, a, D, strict=strict)
            if res is None: continue
            dens, chords, proj = res
            target = 1 / (np.pi**2 * np.sqrt(1 - x * x) * np.sqrt(1 - y * y))
            worst_d = max(worst_d, abs(dens / target - 1)); worst_c = max(worst_c, abs(chords / (4 * proj) - 1))
    return worst_d, worst_c
good = run([(0.5, 1.5), (1.0, 2.0), (3.0, 4.0), (0.2, 1.2), (0.5, 3.0), (2.0, 6.0)])
print(f"disjoint circles: max rel. density error {good[0]:.2e}, max chord-identity error {good[1]:.2e}")
assert good[0] < 1e-5 and good[1] < 1e-9
bad = run([(1.0, 1.0), (0.5, 1.2)], strict=False)
print(f"MUTANT overlapping circles: density error {bad[0]:.2e}, chord error {bad[1]:.2e}")
assert bad[1] > 1e-2, "mutant not rejected"
print("PASS")
