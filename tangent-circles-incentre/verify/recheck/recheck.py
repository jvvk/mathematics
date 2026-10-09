"""Independent recheck for the tangent-circles note (MO 498968).

Shares no code with verify.py, verify_steps.py or verify_sphere_map.py. From the definitions only:

1. P(triangle contains the incentre) = 1/2, by direct barycentric test, for several radius triples;
   each side misses with probability C/(2 pi); misses are disjoint; inner-arc probabilities A/(2 pi).
2. Two circles: the angle subtended by the centres at the crossing point Z is uniform on (pi/2, pi)
   (Kolmogorov-Smirnov), equivalently s = arctan(z/a) + arctan(z/b) uniform on (-pi/2, pi/2).
3. The sphere coordinates: v = |arcsin(sin eta / cos s)| uniform on (0, pi/2) and independent of s
   (chi-square on a 12 x 12 grid).
4. The integral of cos(eta)/sqrt(cos^2 s - sin^2 eta) over |eta| < pi/2 - |s| equals pi (quadrature).
5. Mutants: a wrong threshold (pi - C instead of C) and a wrong angle law must be rejected.

Run: python recheck_note.py [--quick]
"""

from __future__ import annotations

import math
import sys

import numpy as np
from scipy import integrate, stats

QUICK = "--quick" in sys.argv
N = 400_000 if QUICK else 3_000_000
rng = np.random.default_rng(498968)
FAIL: list[str] = []


def check(name: str, ok: bool, detail: str = "") -> None:
    print(f"{'PASS' if ok else 'FAIL'}  {name}  {detail}")
    if not ok:
        FAIL.append(name)


def centres(a: float, b: float, c: float) -> tuple[np.ndarray, np.ndarray, np.ndarray]:
    """Centres of three mutually tangent circles: |AB| = a + b, |AC| = a + c, |BC| = b + c."""
    A = np.array([0.0, 0.0])
    B = np.array([a + b, 0.0])
    x = ((a + c) ** 2 - (b + c) ** 2 + (a + b) ** 2) / (2 * (a + b))
    C = np.array([x, math.sqrt((a + c) ** 2 - x * x)])
    return A, B, C


def angle_at(P, Q, R) -> float:
    u, w = Q - P, R - P
    return math.acos(np.dot(u, w) / (np.linalg.norm(u) * np.linalg.norm(w)))


def on_circle(centre, r, n):
    t = rng.uniform(0, 2 * np.pi, n)
    return centre + r * np.stack([np.cos(t), np.sin(t)], axis=1)


def orient(P, Q, R):
    return (Q[..., 0] - P[..., 0]) * (R[..., 1] - P[..., 1]) - (
        Q[..., 1] - P[..., 1]
    ) * (R[..., 0] - P[..., 0])


# ------------------------------------------------------------------ 1. the theorem
for a, b, c in [(1, 1, 1), (1, 2, 3), (0.1, 1, 5), (2, 7, 0.3)]:
    A, B, C = centres(a, b, c)
    angA, angB, angC = angle_at(A, B, C), angle_at(B, C, A), angle_at(C, A, B)
    la, lb, lc = b + c, a + c, a + b  # opposite side lengths
    I = (la * A + lb * B + lc * C) / (la + lb + lc)
    P, Q, R = on_circle(A, a, N), on_circle(B, b, N), on_circle(C, c, N)
    d1, d2, d3 = orient(P, Q, I[None]), orient(Q, R, I[None]), orient(R, P, I[None])
    contain = ((d1 > 0) & (d2 > 0) & (d3 > 0)) | ((d1 < 0) & (d2 < 0) & (d3 < 0))
    pc = contain.mean()
    se = math.sqrt(0.25 / N)
    check(
        f"P(contain) = 1/2, radii {(a, b, c)}",
        abs(pc - 0.5) < 4 * se,
        f"{pc:.5f} (se {se:.5f})",
    )
    # side XY misses I: segment XY crosses the common tangent of its two circles beyond I
    def miss(X, Y, O1, r1, O2):
        u = (O2 - O1) / np.linalg.norm(O2 - O1)
        T = O1 + r1 * u                                   # contact point
        dX, dY = (X - T) @ u, (Y - T) @ u
        Z = X + (dX / (dX - dY))[:, None] * (Y - X)
        return (Z - I) @ (T - I) < 0
    s_pq = miss(P, Q, A, a, B)
    s_qr = miss(Q, R, B, b, C)
    s_rp = miss(R, P, C, c, A)
    disjoint = not np.any((s_pq & s_qr) | (s_qr & s_rp) | (s_rp & s_pq))
    union_ok = np.array_equal(~contain, s_pq | s_qr | s_rp)
    check(
        f"  misses disjoint and cover the complement, radii {(a, b, c)}",
        disjoint and union_ok,
    )
    naive = [orient(P, Q, I[None]) * orient(P, Q, R) < 0, orient(Q, R, I[None]) * orient(Q, R, P) < 0]
    check(f"  mutant (I across line PQ) is not a disjoint decomposition", bool(np.any(naive[0] & naive[1])))
    for name, ev, ang in [("PQ", s_pq, angC), ("QR", s_qr, angA), ("RP", s_rp, angB)]:
        target = ang / (2 * math.pi)
        sse = math.sqrt(target * (1 - target) / N)
        check(
            f"  side {name} misses w.p. opposite angle/2pi",
            abs(ev.mean() - target) < 4 * sse,
            f"{ev.mean():.5f} vs {target:.5f}",
        )
    # inner arc: vertex inside the incircle
    rho = math.sqrt(a * b * c / (a + b + c))
    inner = np.linalg.norm(P - I, axis=1) < rho
    t = angA / (2 * math.pi)
    check(
        "  P on the inner arc w.p. A/2pi",
        abs(inner.mean() - t) < 4 * math.sqrt(t * (1 - t) / N),
        f"{inner.mean():.5f} vs {t:.5f}",
    )

# ------------------------------------------------------------------ 2. the angle lemma


def crossing(a, b, n):
    """Two circles touching at the origin, centres (-a,0), (b,0); crossing heights z of PQ with x = 0."""
    P = on_circle(np.array([-a, 0.0]), a, n)
    Q = on_circle(np.array([b, 0.0]), b, n)
    lam = P[:, 0] / (P[:, 0] - Q[:, 0])
    z = P[:, 1] + lam * (Q[:, 1] - P[:, 1])
    omega = np.arctan2(Q[:, 1] - P[:, 1], Q[:, 0] - P[:, 0])
    return z, omega


for a, b in [(1, 1), (1, 1.7), (0.3, 4)]:
    z, omega = crossing(a, b, N)
    zp = z[z > 0]
    theta = np.pi - np.arctan(zp / a) - np.arctan(zp / b)  # angle O_A Z O_B
    ks = stats.kstest((theta - np.pi / 2) / (np.pi / 2), "uniform")
    check(
        f"angle O_A Z O_B uniform on (pi/2, pi), radii {(a, b)}",
        ks.pvalue > 1e-3,
        f"KS p = {ks.pvalue:.3f}",
    )
    check(
        "  z > 0 with probability 1/2",
        abs((z > 0).mean() - 0.5) < 4 * math.sqrt(0.25 / N),
    )
    check(
        "  support |z| < sqrt(ab)", bool(np.all(np.abs(z) < math.sqrt(a * b) + 1e-12))
    )
    # mutant: the angle at Z between Z->O_A and the tangent is not uniform
    mut = np.pi / 2 - np.arctan(zp / a)
    ks_m = stats.kstest(mut / (np.pi / 2), "uniform")
    check(
        "  mutant (one-centre angle) rejected",
        ks_m.pvalue < 1e-6,
        f"KS p = {ks_m.pvalue:.1e}",
    )

    # ---------------------------------------------------------- 3. sphere coordinates
    p_, q_ = np.arctan(z / a), np.arctan(z / b)
    s = p_ + q_
    eta = omega - (p_ - q_)
    v = np.abs(np.arcsin(np.clip(np.sin(eta) / np.cos(s), -1, 1)))
    ks_s = stats.kstest((s + np.pi / 2) / np.pi, "uniform")
    ks_v = stats.kstest(v / (np.pi / 2), "uniform")
    H, _, _ = np.histogram2d(
        (s + np.pi / 2) / np.pi, v / (np.pi / 2), bins=12, range=[[0, 1], [0, 1]]
    )
    chi = stats.chisquare(H.ravel())
    check(
        "  sphere: s uniform, v uniform, independent",
        ks_s.pvalue > 1e-3 and ks_v.pvalue > 1e-3 and chi.pvalue > 1e-3,
        f"p = {ks_s.pvalue:.3f}, {ks_v.pvalue:.3f}, chi2 {chi.pvalue:.3f}",
    )
    v_mut = np.abs(eta) / (np.pi / 2 - np.abs(s))
    check(
        "  mutant (linear height) rejected",
        stats.kstest(v_mut, "uniform").pvalue < 1e-6,
    )

# ------------------------------------------------------------------ 4. the integral
worst = 0.0
for s in [0.0, 0.3, -0.7, 1.2, 1.5]:
    e = math.pi / 2 - abs(s)
    # substitute eta = e sin(t) to remove the endpoint singularities
    val, _ = integrate.quad(
        lambda t: (
            math.cos(e * math.sin(t))
            * e
            * math.cos(t)
            / math.sqrt(max(math.cos(s) ** 2 - math.sin(e * math.sin(t)) ** 2, 1e-300))
        ),
        -math.pi / 2,
        math.pi / 2,
        limit=200,
    )
    worst = max(worst, abs(val - math.pi))
check(
    "integral of cos/sqrt(cos^2 s - sin^2) equals pi",
    worst < 1e-6,
    f"max error {worst:.1e}",
)

print()
print("ALL PASS" if not FAIL else f"FAILURES: {FAIL}")
sys.exit(1 if FAIL else 0)
