"""The numerical evidence of Section 6 ("What is left"), each claim asserted.

  sharp     : maximising P over convex n-gons (n = 3..8) from random starts ends at the equilateral triangle
  free      : with the marked point free (any interior point), the maximum is still the equilateral triangle
  stewart   : Stewart's per-cap inequality (each cap of K outside -K has at most the area of the triangle
              G A B on its ends) holds on 1500 random convex polygons (ratio <= 1 up to quadrature error)
  sided     : of 3000 random convex polygons (hulls of 5..10 random points), 2550 are three-sided
  shadow    : P has an interior maximum along a shadow system inside the family of triangles
  steps     : an angular density with five caps of 1/9 each meets Grunbaum's and the Minkowski-Radon
              constraints but has s = 4/9

Usage: python3 searches.py [claim ...]   (default: all). Single core; the whole run takes a few minutes.
"""

from __future__ import annotations

import json
import sys
from pathlib import Path

import numpy as np
from scipy.optimize import minimize
from scipy.spatial import ConvexHull

import exact
from core import kernel, prob, radial, regular

HERE = Path(__file__).resolve().parent
TRI = 1 / 3 + np.log(3) / 6


def hull(x: np.ndarray) -> np.ndarray | None:
    """Convex hull of the points in x, or None if it is (nearly) flat: area / diameter^2 below 1e-4."""
    P = x.reshape(-1, 2)
    try:
        h = ConvexHull(P)
    except Exception:
        return None
    V = P[h.vertices]
    d2 = max(np.sum((V[i] - V[j]) ** 2) for i in range(len(V)) for j in range(i))
    return V if h.volume > 1e-4 * d2 else None


def normalise(x: np.ndarray) -> np.ndarray:
    """Centre and rescale the points (P and s are invariant), so a restart gets a fresh simplex."""
    P = x.reshape(-1, 2)
    P = P - P.mean(0)
    return (P / np.abs(P).max()).ravel()


def sides(V: np.ndarray) -> np.ndarray:
    s = np.linalg.norm(np.roll(V, -1, 0) - V, axis=1)
    return s / s.max()


def thinness(V: np.ndarray) -> float:
    """area / diameter^2: 0 for a segment, 0.433 for an equilateral triangle."""
    d2 = max(np.sum((V[i] - V[j]) ** 2) for i in range(len(V)) for j in range(i))
    return ConvexHull(V).volume / d2


def sharp() -> None:
    """Every restarted run ends at the equilateral triangle or runs off towards a segment; the best is the triangle."""
    rng = np.random.default_rng(11)

    def f(x):
        V = hull(x)
        return 1.0 if V is None else -exact.prob(V)

    for n in range(3, 9):
        ends = {"equilateral": 0, "degenerate": 0}
        best = 0.0
        for _ in range(6):
            x = rng.normal(size=2 * n)
            fx = f(x)
            for _ in range(8):  # Nelder-Mead restarted from its own end point until it stops improving
                r = minimize(f, normalise(x), method="Nelder-Mead",
                             options=dict(maxiter=3000 * n, xatol=1e-9, fatol=1e-12))
                if r.fun > fx - 1e-10:
                    break
                x, fx = r.x, r.fun
            V = hull(x)
            p = exact.prob(V)
            best = max(best, p)
            if len(V) == 3 and np.all(sides(V) > 0.99) and p > TRI - 2e-5:
                ends["equilateral"] += 1
            else:
                assert thinness(V) < 0.02 and p < 0.5 + 1e-3, (n, len(V), thinness(V), p)
                ends["degenerate"] += 1
        assert ends["equilateral"] > 0 and best > TRI - 2e-5
        print(f"sharp: n={n}: runs ending at the equilateral triangle {ends['equilateral']}, "
              f"running off towards a segment {ends['degenerate']}; best P = {best:.6f}")


def free() -> None:
    rng = np.random.default_rng(2)

    def prob_c(V, c, M=1024):
        W = V - c
        E = np.roll(W, -1, axis=0) - W
        nrm = np.stack([E[:, 1], -E[:, 0]], axis=1)
        nrm /= np.linalg.norm(nrm, axis=1)[:, None]
        h = (W * nrm).sum(1)
        if np.any(h <= 1e-6):
            return -1.0
        t = (np.arange(M) + 0.5) * 2 * np.pi / M
        d = np.stack([np.cos(t), np.sin(t)], 1) @ nrm.T
        with np.errstate(divide="ignore"):
            r = np.where(d > 1e-15, h / d, np.inf).min(1)
        rho = r**2
        rho /= rho.sum()
        return float(
            rho @ np.real(np.fft.ifft(np.fft.fft(rho) * np.fft.fft(kernel(M))))
        )

    def f(x, n):
        V = hull(x[2:])
        return 1.0 if V is None else -prob_c(V, x[:2])

    for n in (3, 4, 5, 6):
        best = 0.0
        for _ in range(6):
            x0 = np.concatenate([[0, 0], rng.normal(size=2 * n)])
            r = minimize(
                f,
                x0,
                args=(n,),
                method="Nelder-Mead",
                options=dict(maxiter=6000 * n, xatol=1e-9, fatol=1e-12),
            )
            best = max(best, -r.fun)
        assert best < TRI + 2e-5, (n, best)
        print(
            f"free: n={n}: best P with a free marked point {best:.6f} <= {TRI:.6f} (+ grid error)"
        )


def radial_fn(V: np.ndarray):
    """r(t) about the centroid for any array of angles t, and the area."""
    from core import area_centroid
    A, c = area_centroid(V)
    W = V - c
    E = np.roll(W, -1, axis=0) - W
    nrm = np.stack([E[:, 1], -E[:, 0]], 1)
    nrm /= np.linalg.norm(nrm, axis=1)[:, None]
    h = (W * nrm).sum(1)

    def r(t):
        d = np.stack([np.cos(t), np.sin(t)], 1) @ nrm.T
        with np.errstate(divide="ignore"):
            return np.where(d > 1e-15, h / d, np.inf).min(1)

    return r, A


def caps(V: np.ndarray, M: int = 1 << 14, pieces: int = 400) -> list[tuple[float, float]]:
    """For each cap (alpha, beta), where r(t) > r(t+pi): (its area, area of triangle G A B), as shares of |K|."""
    from scipy.optimize import brentq
    r, A = radial_fn(V)
    g = lambda t: r(np.atleast_1d(t)) - r(np.atleast_1d(t) + np.pi)
    t = 0.123456789 + np.arange(M + 1) * 2 * np.pi / M
    sg = g(t)
    z = [brentq(lambda x: g(x)[0], t[k], t[k + 1], xtol=1e-14) for k in range(M) if sg[k] * sg[k + 1] < 0]
    GX, GW = np.polynomial.legendre.leggauss(40)
    out = []
    for a, b in zip(z, z[1:] + [z[0] + 2 * np.pi]):
        if g((a + b) / 2)[0] <= 0:
            continue
        e = np.linspace(a, b, pieces + 1)
        area = sum((hi - lo) / 2 * GW @ (0.5 * (r((lo + hi) / 2 + (hi - lo) / 2 * GX) ** 2
                                                 - r((lo + hi) / 2 + (hi - lo) / 2 * GX + np.pi) ** 2))
                   for lo, hi in zip(e[:-1], e[1:]))
        ra, rb = r(np.array([a, b]))
        out.append((area / A, 0.5 * ra * rb * np.sin(b - a) / A))
    return out


def stewart() -> None:
    rng = np.random.default_rng(5)
    worst, cnt = 0.0, {}
    for _ in range(1500):
        n = int(rng.integers(4, 12))
        P = rng.normal(size=(n, 2)) * rng.uniform(0.3, 1.5, size=2)
        V = P[ConvexHull(P).vertices]
        cs = caps(V)
        cnt[len(cs)] = cnt.get(len(cs), 0) + 1
        ratio = max(a / b for a, b in cs)
        worst = max(worst, ratio)
        assert sum(b for _, b in cs) * 2 <= exact.phi(V) + 1e-9   # the triangles and their reflections lie in K cap -K
    assert worst < 1 + 1e-7, worst
    print(f"stewart: 1500 polygons, caps per polygon {dict(sorted(cnt.items()))}; max cap/triangle {worst:.9f}")


def crossings(V: np.ndarray) -> int:
    t, r, A = radial(V, 1 << 14)
    d = r - np.roll(r, 1 << 13)
    s = np.sign(d[np.abs(d) > 1e-9 * r.max()])
    return int(np.sum(s != np.roll(s, 1))) // 2


def sided() -> None:
    rng = np.random.default_rng(31)
    cnt: dict[int, int] = {}
    for _ in range(3000):
        n = int(rng.integers(5, 11))
        ang = np.sort(rng.random(n) * 2 * np.pi)
        P = np.stack([np.cos(ang), np.sin(ang)], 1) * rng.uniform(
            0.7, 1.3, size=(n, 1)
        ) + rng.normal(scale=0.15, size=2)
        m = crossings(P[ConvexHull(P).vertices])
        cnt[m] = cnt.get(m, 0) + 1
    assert cnt.get(3) == 2550 and sum(cnt.values()) == 3000, cnt
    print(
        f"sided: crossing pairs m over 3000 random polygons: {dict(sorted(cnt.items()))}"
    )


def shadow() -> None:
    # apex of the equilateral triangle moving parallel to the base: a shadow system of triangles
    ts = np.linspace(-0.6, 0.6, 25)
    vals = [exact.prob(np.array([[-1, 0], [1, 0], [t, np.sqrt(3)]])) for t in ts]
    k = int(np.argmax(vals))
    assert 0 < k < len(ts) - 1 and abs(ts[k]) < 1e-12, (k, ts[k])
    assert vals[k] > max(vals[0], vals[-1]) + 1e-3
    print(
        f"shadow: P along the apex move peaks inside, at t = 0 (P = {vals[k]:.6f}; ends {vals[0]:.6f}, {vals[-1]:.6f})"
    )


def steps() -> None:
    M = 16000  # ten equal arcs of 1600 cells; a half-turn is 8000 cells
    t = (np.arange(M) + 0.5) * 2 * np.pi / M
    kappa = 5 / 9
    sigma = np.where(np.floor(t / (np.pi / 5)) % 2 == 0, 1.0, -1.0)  # ten 36-degree arcs, sigma(t+pi) = -sigma(t)
    rho = (1 + kappa * sigma) / (2 * np.pi)
    dt = 2 * np.pi / M
    assert abs(rho.sum() * dt - 1) < 1e-12
    half = np.array([np.roll(rho, -k)[: M // 2].sum() * dt for k in range(0, M, 20)])
    assert half.max() <= 5 / 9 + 1e-9, half.max()                      # Grunbaum
    ratio = rho / np.roll(rho, M // 2)
    assert ratio.max() <= 4, ratio.max()                                 # Minkowski-Radon
    s = np.minimum(rho, np.roll(rho, M // 2)).sum() * dt
    caps = [((rho - np.roll(rho, M // 2)) * (sigma > 0))[k * M // 10:(k + 1) * M // 10].sum() * dt for k in range(10)]
    assert abs(s - 4 / 9) < 1e-9 and sum(abs(c - 1 / 9) < 1e-9 for c in caps) == 5, (s, caps)
    print(f"steps: max half-plane mass {half.max():.6f} <= 5/9, max ratio {ratio.max():.3f} <= 4, five caps of 1/9, s = {s:.6f}")


CLAIMS = dict(
    sharp=sharp,
    free=free,
    stewart=stewart,
    sided=sided,
    shadow=shadow,
    steps=steps,
)

if __name__ == "__main__":
    for name in sys.argv[1:] or list(CLAIMS):
        CLAIMS[name]()
    print("ALL CLAIMS CHECKED")
