"""MSE 5101873: P(K) = Pr[(X-G).(Y-G) <= 0] for X, Y uniform in a convex polygon K with centroid G.

Angular quadrature: with G = 0, rho(t) = r(t)^2 / (2|K|) is the angular density of a uniform point, and
P = int int rho(s) rho(t) [cos(s - t) <= 0] ds dt (circulant convolution, computed by FFT on M angles).
"""

from __future__ import annotations

import numpy as np
from numpy.typing import NDArray

Arr = NDArray[np.float64]


def area_centroid(V: Arr) -> tuple[float, Arr]:
    x, y = V[:, 0], V[:, 1]
    xs, ys = np.roll(x, -1), np.roll(y, -1)
    cr = x * ys - xs * y
    A = cr.sum() / 2
    c = np.array([((x + xs) * cr).sum(), ((y + ys) * cr).sum()]) / (6 * A)
    return A, c


def radial(V: Arr, M: int) -> tuple[Arr, Arr, float]:
    """Angles t_j (midpoints), r(t_j) about the centroid, and the area. V is a CCW convex polygon."""
    A, c = area_centroid(V)
    W = V - c
    E = np.roll(W, -1, axis=0) - W
    nrm = np.stack([E[:, 1], -E[:, 0]], axis=1)
    nrm /= np.linalg.norm(nrm, axis=1)[:, None]
    h = (W * nrm).sum(1)
    t = (np.arange(M) + 0.5) * 2 * np.pi / M
    U = np.stack([np.cos(t), np.sin(t)], axis=1)
    d = U @ nrm.T
    with np.errstate(divide="ignore"):
        cand = np.where(d > 1e-15, h[None, :] / d, np.inf)
    return t, cand.min(1), A


def kernel(M: int) -> Arr:
    """k_j = [cos(2 pi j / M) <= 0], half weight on the boundary."""
    j = np.arange(M)
    dt = 2 * np.pi * np.minimum(j, M - j) / M
    k = (dt > np.pi / 2 + 1e-12).astype(float)
    k[np.isclose(dt, np.pi / 2)] = 0.5
    return k


def prob(V: Arr, M: int = 4096) -> float:
    t, r, A = radial(V, M)
    rho = r**2 / (2 * A) * (2 * np.pi / M)  # cell masses, sum ~ 1
    rho /= rho.sum()
    conv = np.real(np.fft.ifft(np.fft.fft(rho) * np.fft.fft(kernel(M))))
    return float(rho @ conv)


def half_plane_b(V: Arr, M: int = 4096) -> tuple[Arr, Arr]:
    """t_j, rho mass per cell, and b(t) = a(t) - 1/2, a(t) = mass of {y : y.u_t <= 0}."""
    t, r, A = radial(V, M)
    rho = r**2 / (2 * A) * (2 * np.pi / M)
    rho /= rho.sum()
    a = np.real(np.fft.ifft(np.fft.fft(rho) * np.fft.fft(kernel(M))))
    return t, rho, a - 0.5


def mc(V: Arr, N: int, rng: np.random.Generator) -> float:
    """Independent Monte Carlo: fan triangulation from vertex 0, uniform points."""
    A, c = area_centroid(V)
    tris = [(V[0], V[i], V[i + 1]) for i in range(1, len(V) - 1)]
    w = np.array([abs((b - a)[0] * (d - a)[1] - (b - a)[1] * (d - a)[0]) / 2 for a, b, d in tris])

    def pts() -> Arr:
        k = rng.choice(len(tris), N, p=w / w.sum())
        P0, P1, P2 = (np.array([tris[i][m] for i in k]) for m in range(3))
        u, v = rng.random(N), rng.random(N)
        flip = u + v > 1
        u[flip], v[flip] = 1 - u[flip], 1 - v[flip]
        return P0 + u[:, None] * (P1 - P0) + v[:, None] * (P2 - P0)

    X, Y = pts() - c, pts() - c
    return float(np.mean((X * Y).sum(1) <= 0))


def regular(n: int) -> Arr:
    t = 2 * np.pi * np.arange(n) / n
    return np.stack([np.cos(t), np.sin(t)], axis=1)
