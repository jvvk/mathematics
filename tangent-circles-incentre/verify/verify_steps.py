"""Step-by-step checks for ANSWER.md not covered by verify.py. Each check has a mutant that must fail.

Step 1: incircle touches AB at the contact point; I outside every circle; IT_C, IT_B tangent to Gamma_A;
        directions to Gamma_A fill exactly angle pi - A; the three sector angles sum to 2 pi.
Step 3: (a) pointwise density f(z) vs histogram, both signs of z; (b) Jacobian by finite differences;
        (c) m_A + m_B = (a+b) cos w and |PQ| = |ZP| + |ZQ|; (d) half-chord closed forms;
        (e) f(z) = (a+b)/pi^2 * int cos^2 w / (c_A c_B) dw vs closed form; (f) tidying identity;
        (g) chord-existence interval and z^2 < ab.
Step 4: angle T_C A I = A/2; tan(A/2) tan(B/2) = rho^2/(ab); P(z > rho) = P(z < -rho) (symmetry).
"""

from __future__ import annotations

import numpy as np
from scipy.integrate import quad

rng = np.random.default_rng(23)


def cr2(u, v):
    return u[..., 0] * v[..., 1] - u[..., 1] * v[..., 0]

ok = True


def chk(name: str, good: bool, detail: str = "") -> None:
    global ok
    ok &= bool(good)
    print(f"{'PASS' if good else 'FAIL'}  {name} {detail}")


def mutant(name: str, survives: bool) -> None:
    chk(f"mutant rejected: {name}", not survives)


# ---------------- Step 1 ----------------
def triangle(a: float, b: float, c: float):
    A, B = np.array([0.0, 0.0]), np.array([a + b, 0.0])
    x = ((a + c) ** 2 - (b + c) ** 2 + (a + b) ** 2) / (2 * (a + b))
    C = np.array([x, np.sqrt((a + c) ** 2 - x ** 2)])
    I = ((b + c) * A + (a + c) * B + (a + b) * C) / (2 * (a + b + c))
    return A, B, C, I


def angle(U, V, W):
    return np.arccos(np.clip(np.dot(V - U, W - U) / np.linalg.norm(V - U) / np.linalg.norm(W - U), -1, 1))


for a, b, c in [(1, 1, 1), (1, 2, 3), (0.1, 1, 5), (2, 7, 0.3)]:
    A, B, C, I = triangle(a, b, c)
    TC, TB, TA = A + (B - A) * a / (a + b), A + (C - A) * a / (a + c), B + (C - B) * b / (b + c)
    rho = np.sqrt(a * b * c / (a + b + c))
    dists = [abs(cr2(B - A, I - A)) / np.linalg.norm(B - A), np.linalg.norm(I - TC)]
    chk(f"incircle touches AB at T_C {a,b,c}", np.allclose(dists, rho) and abs(np.dot(I - TC, B - A)) < 1e-12)
    chk(f"I outside all circles {a,b,c}", all(np.linalg.norm(I - X) > r for X, r in [(A, a), (B, b), (C, c)]))
    chk(f"IT_C, IT_B tangent to Gamma_A {a,b,c}",
        abs(np.dot(I - TC, TC - A)) < 1e-12 and abs(np.dot(I - TB, TB - A)) < 1e-12)
    # directions from I to Gamma_A: angular width of the sampled set vs pi - A
    t = np.linspace(0, 2 * np.pi, 400001)
    pts = A + a * np.stack([np.cos(t), np.sin(t)], 1)
    axis = (A - I) / np.linalg.norm(A - I)
    rel = np.arctan2(cr2(axis, pts - I), (pts - I) @ axis)
    width = rel.max() - rel.min()
    angA, angB, angC = angle(A, B, C), angle(B, C, A), angle(C, A, B)
    chk(f"Gamma_A seen from I fills pi - A {a,b,c}", abs(width - (np.pi - angA)) < 1e-6, f"{width:.6f} vs {np.pi-angA:.6f}")
    s = angle(I, TC, TB) + angle(I, TA, TC) + angle(I, TB, TA)
    chk(f"sectors sum to 2 pi {a,b,c}", abs(s - 2 * np.pi) < 1e-9)
    chk(f"angle T_C A I = A/2 {a,b,c}", abs(angle(A, TC, I) - angA / 2) < 1e-9)
    chk(f"tan(A/2)tan(B/2) = rho^2/ab < 1 {a,b,c}",
        abs(np.tan(angA / 2) * np.tan(angB / 2) - rho ** 2 / (a * b)) < 1e-12 and rho < np.sqrt(a * b))
    mutant(f"I = centroid instead of incentre {a,b,c}",
           np.allclose([abs(cr2(B - A, (A + B + C) / 3 - A)) / np.linalg.norm(B - A)], rho) and a != b)


# ---------------- Step 3 ----------------
def cross_z(a, b, th, ph):
    px, py = -a + a * np.cos(th), a * np.sin(th)
    qx, qy = b + b * np.cos(ph), b * np.sin(ph)
    return (py * qx - qy * px) / (qx - px)


def omega(a, b, th, ph):
    px, py = -a + a * np.cos(th), a * np.sin(th)
    qx, qy = b + b * np.cos(ph), b * np.sin(ph)
    return np.arctan2(qy - py, qx - px)  # direction of PQ (positive x-component)


f = lambda z, a, b: (a / (a * a + z * z) + b / (b * b + z * z)) / np.pi * (np.abs(z) < np.sqrt(a * b))

for a, b in [(1, 1), (1, 3), (0.2, 5)]:
    # (a) histogram vs density, both signs
    z = cross_z(a, b, rng.uniform(0, 2 * np.pi, 8_000_000), rng.uniform(0, 2 * np.pi, 8_000_000))
    L = np.sqrt(a * b)
    edges = np.linspace(-L, L, 41)
    h, _ = np.histogram(z, edges)
    emp = h / len(z)
    th_ = np.array([quad(f, e0, e1, args=(a, b))[0] for e0, e1 in zip(edges[:-1], edges[1:])])
    se = np.sqrt(th_ * (1 - th_) / len(z))
    chk(f"density histogram 40 bins a={a} b={b}", np.max(np.abs(emp - th_) / se) < 5,
        f"max |dev|/se = {np.max(np.abs(emp - th_) / se):.2f}")
    chk(f"P(z>r)=P(z<-r) a={a} b={b}", abs(np.mean(z > 0.5 * L) - np.mean(z < -0.5 * L)) < 0.001)
    wrong = (a / (a * a + ((edges[:-1] + edges[1:]) / 2) ** 2)) * 2 / np.pi * np.diff(edges)  # Cauchy(a) only
    mutant(f"density = Cauchy(a) alone a={a} b={b}", np.max(np.abs(emp - wrong) / se) < 5 and a != b)

    # (b) Jacobian: |d(z,w)/d(th,ph)| = c_A c_B / (cos w |PQ|)
    jac_mut: list[bool] = []
    for _ in range(5):
        while True:
            th, ph = rng.uniform(0, 2 * np.pi, 2)
            if abs(np.cos(omega(a, b, th, ph))) > 0.05:
                break
        e = 1e-6
        J = np.array([[(cross_z(a, b, th + e, ph) - cross_z(a, b, th - e, ph)) / (2 * e),
                       (cross_z(a, b, th, ph + e) - cross_z(a, b, th, ph - e)) / (2 * e)],
                      [(omega(a, b, th + e, ph) - omega(a, b, th - e, ph)) / (2 * e),
                       (omega(a, b, th, ph + e) - omega(a, b, th, ph - e)) / (2 * e)]])
        zz, w = cross_z(a, b, th, ph), omega(a, b, th, ph)
        P = np.array([-a + a * np.cos(th), a * np.sin(th)]); Q = np.array([b + b * np.cos(ph), b * np.sin(ph)])
        Z = np.array([0.0, zz]); u = np.array([np.cos(w), np.sin(w)])
        mA, mB = abs((np.array([-a, 0]) - Z) @ u), abs((np.array([b, 0]) - Z) @ u)
        cA, cB = np.sqrt(mA ** 2 - zz ** 2), np.sqrt(mB ** 2 - zz ** 2)
        PQ = np.linalg.norm(Q - P)
        pred = cA * cB / (np.cos(w) * PQ)
        chk(f"Jacobian a={a} b={b}", abs(abs(np.linalg.det(J)) - pred) < 1e-6 * pred,
            f"{abs(np.linalg.det(J)):.6f} vs {pred:.6f}")
        jac_mut.append(abs(abs(np.linalg.det(J)) - cA * cB / PQ) < 1e-5 * pred)
        # (c) projection identity and Z between chords
        chk(f"m_A+m_B=(a+b)cos w, |PQ|=|ZP|+|ZQ| a={a} b={b}",
            abs(mA + mB - (a + b) * np.cos(w)) < 1e-9 and abs(PQ - np.linalg.norm(P - Z) - np.linalg.norm(Q - Z)) < 1e-9)
        # (d) half-chord closed forms (with z>0 or z<0: p, q signed)
        p, q = np.arctan(zz / a), np.arctan(zz / b)
        cA2 = a * a * np.cos(w) * np.cos(w - 2 * p) / np.cos(p) ** 2
        cB2 = b * b * np.cos(w) * np.cos(w + 2 * q) / np.cos(q) ** 2
        chk(f"half-chords a={a} b={b}", abs(cA2 - cA ** 2) < 1e-9 and abs(cB2 - cB ** 2) < 1e-9)
        mutant("half-chord with cos(w+2p)", abs(a * a * np.cos(w) * np.cos(w + 2 * p) / np.cos(p) ** 2 - cA ** 2) < 1e-9)

    mutant(f"Jacobian without cos w (all 5 samples) a={a} b={b}", all(jac_mut))

    # (e) the integral representation of f before simplification, and (g) the interval
    for zz in [0.1 * L, 0.5 * L, 0.9 * L]:
        p, q = np.arctan(zz / a), np.arctan(zz / b)
        lo, hi = 2 * p - np.pi / 2, np.pi / 2 - 2 * q

        def integrand(w):
            mA, mB = a * np.cos(w) + zz * np.sin(w), b * np.cos(w) - zz * np.sin(w)
            return np.cos(w) ** 2 / np.sqrt((mA ** 2 - zz ** 2) * (mB ** 2 - zz ** 2))

        val = (a + b) / np.pi ** 2 * quad(integrand, lo, hi, limit=400)[0]
        chk(f"f(z) integral form a={a} b={b} z={zz:.3f}", abs(val - f(zz, a, b)) < 1e-6, f"{val:.7f} vs {f(zz,a,b):.7f}")
        # (f) tidying chain
        t1 = np.sin(p + q) * np.cos(p - q) / (np.pi * zz)
        t2 = (np.sin(2 * p) + np.sin(2 * q)) / (2 * np.pi * zz)
        chk(f"tidying a={a} b={b} z={zz:.3f}", abs(t1 - f(zz, a, b)) < 1e-12 and abs(t2 - f(zz, a, b)) < 1e-12)
        # (g) both chords exist exactly on (lo, hi): check just inside and just outside
        def chords(w):
            mA, mB = a * np.cos(w) + zz * np.sin(w), b * np.cos(w) - zz * np.sin(w)
            return mA > 0 and mB > 0 and mA ** 2 > zz ** 2 and mB ** 2 > zz ** 2
        chk(f"chord interval a={a} b={b} z={zz:.3f}",
            chords(lo + 1e-7) and chords(hi - 1e-7) and not chords(lo - 1e-7) and not chords(hi + 1e-7))
    mutant(f"f without the 4-to-1 factor a={a} b={b}", abs(val / 4 - f(zz, a, b)) < 1e-6)

print("ALL PASS" if ok else "SOME FAILED")
