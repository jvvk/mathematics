"""Checks for the tangent-circles incentre proof (MO 498968, MSE 5084455/5086572/5087823).

1. Pair lemma: for circles radii a, b tangent at T, the point z where PQ crosses the common tangent
   has density (1/pi)(a/(a^2+z^2) + b/(b^2+z^2)) on |z| < sqrt(ab), i.e. P(0<z<r) = (p+q)/pi with
   tan p = r/a, tan q = r/b. Checked against simulation, with a mutant density that must fail.
2. The integral step: int cos(w) dw / sqrt(cos(w-2p) cos(w+2q)) over the valid range equals
   pi cos(p-q), checked by quadrature.
3. Triangle: per sample, "I not in PQR" == "exactly one pair event z > rho" and the pair events are
   disjoint; P(E_C) = C/(2 pi); P(I in PQR) = 1/2. Mutant: using the wrong side (z < -rho) must fail.
"""

from __future__ import annotations

import numpy as np
from scipy.integrate import quad

rng = np.random.default_rng(11)
N = 8_000_000
ok = True


def check(name: str, got: float, want: float, tol: float) -> bool:
    good = abs(got - want) < tol
    print(f"{'PASS' if good else 'FAIL'}  {name}: got {got:.5f}, want {want:.5f}")
    return good


def crossing(a: float, b: float, n: int) -> np.ndarray:
    """T at origin, common tangent = y-axis, A=(-a,0), B=(b,0). Height where PQ meets x=0."""
    t, s = rng.uniform(0, 2 * np.pi, n), rng.uniform(0, 2 * np.pi, n)
    px, py = -a + a * np.cos(t), a * np.sin(t)
    qx, qy = b + b * np.cos(s), b * np.sin(s)
    return (py * qx - qy * px) / (qx - px)


# 1. pair lemma
for a, b in [(1, 1), (1, 3), (0.2, 5)]:
    z = crossing(a, b, N)
    ok &= check(f"support |z|<=sqrt(ab) a={a} b={b}", float(np.abs(z).max() <= np.sqrt(a * b) + 1e-9), 1, 0.5)
    for r in [0.3 * np.sqrt(a * b), 0.8 * np.sqrt(a * b)]:
        want = (np.arctan(r / a) + np.arctan(r / b)) / np.pi
        ok &= check(f"P(0<z<r) a={a} b={b} r={r:.3f}", float(np.mean((z > 0) & (z < r))), want, 0.002)
        mutant = 2 * np.arctan(r / np.sqrt(a * b)) / np.pi  # plausible wrong guess: one Cauchy of scale sqrt(ab)
        if a != b:
            bad = abs(np.mean((z > 0) & (z < r)) - mutant) > 0.002
            print(f"{'PASS' if bad else 'FAIL'}  mutant density rejected a={a} b={b} r={r:.3f}")
            ok &= bad

# 2. the integral collapsing to pi cos(p-q)
for p, q in [(0.3, 0.5), (0.1, 1.2), (0.7, 0.7)]:
    lo, hi = 2 * p - np.pi / 2, np.pi / 2 - 2 * q
    val, _ = quad(lambda w: np.cos(w) / np.sqrt(np.cos(w - 2 * p) * np.cos(w + 2 * q)), lo, hi, limit=200)
    ok &= check(f"integral p={p} q={q}", val, np.pi * np.cos(p - q), 1e-6)

# 3. triangle
for a, b, c in [(1, 1, 1), (1, 2, 3), (0.1, 1, 5), (2, 7, 0.3)]:
    A, B = np.array([0.0, 0.0]), np.array([a + b, 0.0])
    x = ((a + c) ** 2 - (b + c) ** 2 + (a + b) ** 2) / (2 * (a + b))
    C = np.array([x, np.sqrt((a + c) ** 2 - x ** 2)])
    I = ((b + c) * A + (a + c) * B + (a + b) * C) / (2 * (a + b + c))
    ang = lambda U, V, W: np.arccos(np.dot(V - U, W - U) / np.linalg.norm(V - U) / np.linalg.norm(W - U))
    angs = {"A": ang(A, B, C), "B": ang(B, C, A), "C": ang(C, A, B)}
    rho = np.sqrt(a * b * c / (a + b + c))

    def pts(ctr, r):
        t = rng.uniform(0, 2 * np.pi, N)
        return ctr + r * np.stack([np.cos(t), np.sin(t)], 1)

    P, Q, R = pts(A, a), pts(B, b), pts(C, c)

    rad = {id(A): a, id(B): b, id(C): c}

    def event(U, V, X, Y):
        """Segment UV meets the common tangent of circles X, Y beyond I (more than rho from T)."""
        nrm = (Y - X) / np.linalg.norm(Y - X)
        T = X + rad[id(X)] * nrm
        d = (I - T) / np.linalg.norm(I - T)
        su, sv = (U - T) @ nrm, (V - T) @ nrm
        Z = U + (su / (su - sv))[:, None] * (V - U)
        return (Z - T) @ d > rho

    EC, EA, EB = event(P, Q, A, B), event(Q, R, B, C), event(R, P, C, A)
    cr = lambda u, v: u[:, 0] * v[:, 1] - u[:, 1] * v[:, 0]
    u, v, w = cr(Q - P, I - P), cr(R - Q, I - Q), cr(P - R, I - R)
    inside = ((u > 0) & (v > 0) & (w > 0)) | ((u < 0) & (v < 0) & (w < 0))
    cnt = EA.astype(int) + EB + EC
    ok &= check(f"disjoint pair events {a,b,c}", float(cnt.max()), 1, 0.5)
    ok &= check(f"miss == one pair event {a,b,c}", float(np.mean((cnt == 1) == ~inside)), 1, 1e-9)
    for nm, E in [("C", EC), ("A", EA), ("B", EB)]:
        ok &= check(f"P(E_{nm}) {a,b,c}", float(E.mean()), angs[nm] / (2 * np.pi), 0.0008)
    ok &= check(f"P(I in PQR) {a,b,c}", float(inside.mean()), 0.5, 0.0008)
    # mutant: wrong side of I (towards T) must not reproduce containment
    T = A + (B - A) / (a + b) * a
    d = (I - T) / np.linalg.norm(I - T)
    Z = P + ((P - T) @ ((B - A) / (a + b)) / (((P - T) - (Q - T)) @ ((B - A) / (a + b))))[:, None] * (Q - P)
    wrong = (((Z - T) @ d) < rho) & (((Z - T) @ d) > 0)
    bad = np.mean(wrong == EC) < 0.99
    print(f"{'PASS' if bad else 'FAIL'}  mutant side rejected {a,b,c}")
    ok &= bad

print("ALL PASS" if ok else "SOME FAILED")
