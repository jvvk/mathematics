"""Marked broken-stick tetrahedron probability p_m (MO q/142983), by deterministic quadrature.

Reduction (see STATUS.md):
  Lengths of a stick broken at 5 uniform points are Dirichlet(1,...,1); the tetrahedron condition is
  scale-invariant, so p_m = P(six iid Exp(1) lengths, placed on fixed edges, form a tetrahedron).
  Edges: a = 12, b = 13, C = 23 (face 123), c = 14, B = 24 (face 124), A = 34.
  Hinge faces 123 and 124 on edge 12: A ranges exactly over (Amin, Amax) = (|P3 - P4|, |P3 - conj P4|),
  P3, P4 the apexes in the upper half plane with a = 1 on the real axis from 0 to 1.
  Integrating A out and scaling out a:
      p_m = 24 * int db dC dc dB [G(Amin) - G(Amax)],   G(x) = (K + x)^-5,  K = 1 + b + C + c + B.
  Elliptic coordinates P = f(z) = (1 + cosh z)/2, z = mu + i nu, mu > 0, 0 < nu < pi:
      b + C = cosh mu, b - C = cos nu, db dC = (1/2) sinh mu sin nu dmu dnu.
  f is injective on mu > 0, -pi < nu < pi and f(conj z) = conj f(z), so the Amax term is the Amin term with z'
  in the lower half-strip, where sin nu' < 0 supplies the minus sign:
      p_m = 6 * int_{z in R+} int_{z' in R} sinh mu sin nu sinh mu' sin nu' G(|f(z) - f(z')|) ,
  R = (0, M) x (-pi, pi). The only non-smooth point is z' = z; polar coordinates around z remove it.
"""

from __future__ import annotations

import sys

import numpy as np

M = 16.0  # mu cutoff: integrand decays like exp(-4 mu); exp(-64) is far below double precision


def gl(n: int, a: float, b: float) -> tuple[np.ndarray, np.ndarray]:
    x, w = np.polynomial.legendre.leggauss(n)
    return 0.5 * (b - a) * x + 0.5 * (b + a), 0.5 * (b - a) * w


def composite(n: int, cuts: list[float]) -> tuple[np.ndarray, np.ndarray]:
    xs, ws = zip(*(gl(n, a, b) for a, b in zip(cuts[:-1], cuts[1:])))
    return np.concatenate(xs), np.concatenate(ws)


def f(z: np.ndarray) -> np.ndarray:
    return 0.5 * (1.0 + np.cosh(z))


def inner(z: complex, n: int, sign_mutant: bool = False) -> float:
    """int_{z' in R} sinh mu' sin nu' G(|f(z)-f(z')|) d^2z', polar around z, sectors split at the corners of R."""
    mu, nu = z.real, z.imag
    corners = [
        complex(0, -np.pi),
        complex(M, -np.pi),
        complex(M, np.pi),
        complex(0, np.pi),
    ]
    ang = np.sort(np.array([np.angle(c - z) for c in corners]))
    ang = np.append(ang, ang[0] + 2 * np.pi)
    fz = f(np.array(z))
    Kz = 1.0 + np.cosh(mu)
    total = 0.0
    for a0, a1 in zip(ang[:-1], ang[1:]):
        phi, wphi = gl(n, a0, a1)
        mid = 0.5 * (a0 + a1)
        c, s = np.cos(mid), np.sin(mid)
        # exiting side for this sector (constant inside the sector)
        cand = []
        if c < 0:
            cand.append(("mu0", -mu / c))
        if c > 0:
            cand.append(("muM", (M - mu) / c))
        if s > 0:
            cand.append(("nupi", (np.pi - nu) / s))
        if s < 0:
            cand.append(("num", (-np.pi - nu) / s))
        side = min(cand, key=lambda t: t[1])[0]
        cp, sp = np.cos(phi), np.sin(phi)
        R = {
            "mu0": -mu / cp,
            "muM": (M - mu) / cp,
            "nupi": (np.pi - nu) / sp,
            "num": (-np.pi - nu) / sp,
        }[side]
        # rho: composite GL on geometric pieces so the exp decay along long rays is resolved
        t, wt = composite(n, [0.0, 0.05, 0.25, 1.0])
        rho = R[:, None] * t[None, :]
        wr = R[:, None] * wt[None, :]
        zp = z + rho * np.exp(1j * phi)[:, None]
        mup, nup = zp.real, zp.imag
        wgt = np.sinh(mup) * (np.abs(np.sin(nup)) if sign_mutant else np.sin(nup))
        A = np.abs(fz - f(zp))
        K = Kz + np.cosh(mup)
        total += float(np.sum(wphi[:, None] * wr * rho * wgt * (K + A) ** -5))
    return total


def p_marked(n: int, sign_mutant: bool = False) -> float:
    mus, wmu = composite(n, [0.0, 0.5, 1.5, 3.5, 7.0, M])
    nus, wnu = gl(n, 0.0, np.pi)
    tot = 0.0
    for m, wm in zip(mus, wmu):
        for v, wv in zip(nus, wnu):
            tot += (
                wm * wv * np.sinh(m) * np.sin(v) * inner(complex(m, v), n, sign_mutant)
            )
    return 6.0 * tot


def triangle_control(n: int) -> float:
    """Same weights and coordinates for the 2D analogue: p = 2 int db dC (1+b+C)^-3 = 1/4 exactly."""
    mus, wmu = composite(n, [0.0, 0.5, 1.5, 3.5, 7.0, M])
    nus, wnu = gl(n, 0.0, np.pi)
    g = np.sinh(mus) * (1 + np.cosh(mus)) ** -3
    return float(2 * 0.5 * np.sum(wmu * g) * np.sum(wnu * np.sin(nus)))


def monte_carlo(N: int, seed: int = 1) -> tuple[float, float]:
    rng = np.random.default_rng(seed)
    hits = 0
    for _ in range(N // 10**6):
        a, b, c, A, B, C = rng.exponential(size=(6, 10**6))
        # Cayley-Menger: 288 V^2 > 0 plus the four face triangle inequalities
        d = [x * x for x in (a, b, c, A, B, C)]
        a2, b2, c2, A2, B2, C2 = d
        cm = (
            a2 * A2 * (b2 + c2 + B2 + C2 - a2 - A2)
            + b2 * B2 * (a2 + c2 + A2 + C2 - b2 - B2)
            + c2 * C2 * (a2 + b2 + A2 + B2 - c2 - C2)
            - a2 * b2 * C2
            - a2 * c2 * B2
            - b2 * c2 * A2
            - A2 * B2 * C2
        )
        tri = lambda x, y, z: (x < y + z) & (y < x + z) & (z < x + y)
        ok = (cm > 0) & tri(a, b, C) & tri(a, c, B) & tri(b, c, A) & tri(A, B, C)
        hits += int(ok.sum())
    p = hits / N
    return p, (p * (1 - p) / N) ** 0.5


def D2(mu1, nu1, mu2, nu2):
    """Smooth periodic squared distance on the cylinder, invariant under simultaneous negation."""
    return (mu1 - mu2) ** 2 + 2.0 * (1.0 - np.cos(nu1 - nu2))


def inner_cyl(z: complex, n: int, k: int = 2) -> float:
    """inner(z) via the full cylinder mu' in (-M, M), nu' periodic (the integrand is even under z' -> -z' and
    2 pi periodic in nu'). Kinks at z and -z; chi = D^2k(z',-z) / (D^2k(z',-z) + D^2k(z',z)) keeps the one at z,
    and chi(z') + chi(-z') = 1 gives int_cyl F chi = (1/2) int_cyl F = int_{mu'>0} F. Polar around z on the
    rectangle [-M, M] x [nu - pi, nu + pi]; the seam is pi away from z."""
    mu, nu = z.real, z.imag
    lo, hi = nu - np.pi, nu + np.pi
    corners = [complex(-M, lo), complex(M, lo), complex(M, hi), complex(-M, hi)]
    ang = np.sort(np.array([np.angle(c - z) for c in corners]))
    ang = np.append(ang, ang[0] + 2 * np.pi)
    fz = f(np.array(z))
    Kz = 1.0 + np.cosh(mu)
    total = 0.0
    t, wt = composite(n, [0.0, 0.03, 0.1, 0.25, 0.5, 1.0])
    for a0, a1 in zip(ang[:-1], ang[1:]):
        phi, wphi = gl(n, a0, a1)
        mid = 0.5 * (a0 + a1)
        c, s = np.cos(mid), np.sin(mid)
        cand = []
        if c < 0:
            cand.append(("m0", (-M - mu) / c))
        if c > 0:
            cand.append(("mM", (M - mu) / c))
        if s > 0:
            cand.append(("hi", np.pi / s))
        if s < 0:
            cand.append(("lo", -np.pi / s))
        side = min(cand, key=lambda q: q[1])[0]
        cp, sp = np.cos(phi), np.sin(phi)
        R = {"m0": (-M - mu) / cp, "mM": (M - mu) / cp, "hi": np.pi / sp, "lo": -np.pi / sp}[side]
        rho = R[:, None] * t[None, :]
        wr = R[:, None] * wt[None, :]
        zp = z + rho * np.exp(1j * phi)[:, None]
        mup, nup = zp.real, zp.imag
        dm = D2(mup, nup, -mu, -nu) ** k
        chi = dm / (dm + D2(mup, nup, mu, nu) ** k)
        F = np.sinh(mup) * np.sin(nup) * (Kz + np.cosh(mup) + np.abs(fz - f(zp))) ** -5
        total += float(np.sum(wphi[:, None] * wr * rho * F * chi))
    return total


def p_marked_cyl(n: int, nout: int | None = None, k: int = 2) -> float:
    nout = nout or n
    mus, wmu = composite(nout, [0.0, 0.1, 0.5, 1.5, 3.5, 7.0, M])
    nus, wnu = composite(nout, [0.0, 0.1, np.pi / 2, np.pi - 0.1, np.pi])
    tot = 0.0
    for m, wm in zip(mus, wmu):
        for v, wv in zip(nus, wnu):
            tot += wm * wv * np.sinh(m) * np.sin(v) * inner_cyl(complex(m, v), n, k)
    return 6.0 * tot


if __name__ == "__main__":
    mode = sys.argv[1]
    if mode == "control":
        for n in (8, 16, 32):
            print("triangle", n, repr(triangle_control(n)), "target 0.25")
    elif mode == "mc":
        print("mc", *monte_carlo(int(float(sys.argv[2]))))
    elif mode == "quad":
        n = int(sys.argv[2])
        print("quad", n, repr(p_marked(n, sign_mutant=len(sys.argv) > 3)))
    elif mode == "cyl":
        # the method behind the stated value: p_marked_cyl(inner order, outer order)
        n, nout = int(sys.argv[2]), int(sys.argv[3])
        print("cyl", n, nout, repr(p_marked_cyl(n, nout)))
