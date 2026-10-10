"""Robust evaluators for convex polygons (no fixed angular grid, so thin shapes are safe).

P(K) = int rho(t) a(t) dt, rho(t) = r(t)^2 / (2|K|) about the centroid, a(t) = |K cap {y.u_t <= 0}| / |K|.
Both factors are analytic between breakpoints (vertex directions and those +- pi/2), so Gauss-Legendre on each
piece is essentially exact. Phi(K) = |K cap (2c - K)| / |K| by convex clipping.
"""

from __future__ import annotations

import numpy as np
from numpy.typing import NDArray

from core import area_centroid

Arr = NDArray[np.float64]
GX, GW = np.polynomial.legendre.leggauss(24)
GX2, GW2 = np.polynomial.legendre.leggauss(48)


def _halfplane_area(W: Arr, u: Arr) -> float:
    """Area of the CCW convex polygon W (centred) intersected with {y : y.u <= 0}."""
    s = W @ u
    pts = []
    n = len(W)
    for j in range(n):
        p, q, sp, sq = W[j], W[(j + 1) % n], s[j], s[(j + 1) % n]
        if sp <= 0:
            pts.append(p)
        if sp * sq < 0:
            pts.append(p + (q - p) * sp / (sp - sq))
    if len(pts) < 3:
        return 0.0
    Q = np.array(pts)
    return 0.5 * float(
        np.sum(Q[:, 0] * np.roll(Q[:, 1], -1) - np.roll(Q[:, 0], -1) * Q[:, 1])
    )


def halfplane_areas(W: Arr, ts: Arr) -> Arr:
    """Areas of W (CCW convex, origin inside) intersected with {y : y.u_t <= 0}, for every t in ts at once.

    The origin lies on the cutting line, so the region is the fan of triangles (0, p', q') over the edges
    (p, q) clipped to the half-plane: clip each edge parametrically and add the signed areas.
    """
    U = np.stack([np.cos(ts), np.sin(ts)], 1)            # (T, 2)
    P, Q = W, np.roll(W, -1, axis=0)                      # edges p -> q, (n, 2)
    sp, sq = U @ P.T, U @ Q.T                             # (T, n)
    lam = np.where(np.abs(sp - sq) > 0, sp / np.where(np.abs(sp - sq) > 0, sp - sq, 1), 0.0)
    lam = np.clip(lam, 0.0, 1.0)                          # crossing parameter along p -> q
    # clipped endpoints: keep p if sp <= 0 else move to crossing; keep q if sq <= 0 else move to crossing
    a0 = np.where(sp <= 0, 0.0, lam)                      # start parameter of the kept part
    a1 = np.where(sq <= 0, 1.0, lam)                      # end parameter of the kept part
    keep = ~((sp > 0) & (sq > 0))
    D = Q - P
    x0 = P[None, :, 0] + a0 * D[None, :, 0]
    y0 = P[None, :, 1] + a0 * D[None, :, 1]
    x1 = P[None, :, 0] + a1 * D[None, :, 0]
    y1 = P[None, :, 1] + a1 * D[None, :, 1]
    return 0.5 * np.sum(np.where(keep, x0 * y1 - x1 * y0, 0.0), axis=1)


def _adaptive(f, lo: float, hi: float, tol: float) -> float:
    """Adaptive Gauss-Legendre on [lo, hi] for a vectorised f: an interval is accepted when its 24- and
    48-point rules agree to tol times its share of the range, and bisected otherwise."""
    total, stack, n = 0.0, [(lo, hi)], 0
    while stack:
        a, b = stack.pop()
        m, hw = (a + b) / 2, (b - a) / 2
        v24 = hw * float(GW @ f(m + hw * GX))
        v48 = hw * float(GW2 @ f(m + hw * GX2))
        n += 1
        if abs(v24 - v48) <= tol * max(1.0, abs(b - a)) or n > 200000:
            total += v48
        else:
            stack += [(a, m), (m, b)]
    if n > 200000:
        raise RuntimeError("quadrature did not converge")
    return total


def prob(V: Arr, tol: float = 1e-13) -> float:
    """P(K) for a CCW convex polygon V, about its centroid.

    Between consecutive breakpoints (vertex directions and those +- pi/2) the ray in direction t meets one edge
    k, so rho(t) dt = h_k^2 sec^2(t - phi_k) dt / (2|K|) with phi_k the direction of that edge's normal. With
    u = tan(t - phi_k) this is h_k^2 du / (2|K|): the near-pole of sec^2 on thin shapes is gone. a(t) is then
    integrated in u by adaptive Gauss-Legendre (24 against 48 points, bisecting where they disagree).
    """
    A, c = area_centroid(V)
    W = V - c
    E = np.roll(W, -1, axis=0) - W
    nrm = np.stack([E[:, 1], -E[:, 0]], axis=1)
    nrm /= np.linalg.norm(nrm, axis=1)[:, None]
    h = (W * nrm).sum(1)
    phi = np.arctan2(nrm[:, 1], nrm[:, 0])
    va = np.arctan2(W[:, 1], W[:, 0])
    br = np.sort(np.mod(np.concatenate([va, va + np.pi / 2, va - np.pi / 2]), 2 * np.pi))
    br = np.concatenate([br, [br[0] + 2 * np.pi]])
    total = 0.0
    for lo, hi in zip(br[:-1], br[1:]):
        if hi - lo < 1e-15:
            continue
        mid = (lo + hi) / 2
        d = nrm @ np.array([np.cos(mid), np.sin(mid)])
        k = int(np.argmin(np.where(d > 1e-15, h / np.where(d > 1e-15, d, 1), np.inf)))
        ulo = np.tan((lo - phi[k] + np.pi) % (2 * np.pi) - np.pi)
        uhi = np.tan((hi - phi[k] + np.pi) % (2 * np.pi) - np.pi)
        val = _adaptive(lambda us: halfplane_areas(W, phi[k] + np.arctan(us)) / A, ulo, uhi, tol)
        total += h[k] ** 2 / (2 * A) * val
    return total


def clip(P: Arr, Q: Arr) -> Arr:
    """Sutherland-Hodgman: CCW convex P clipped by CCW convex Q."""
    out = list(P)
    for k in range(len(Q)):
        a, b = Q[k], Q[(k + 1) % len(Q)]
        inp, out = out, []
        for j in range(len(inp)):
            p, q = inp[j], inp[(j + 1) % len(inp)]
            sp = (b[0] - a[0]) * (p[1] - a[1]) - (b[1] - a[1]) * (p[0] - a[0])
            sq = (b[0] - a[0]) * (q[1] - a[1]) - (b[1] - a[1]) * (q[0] - a[0])
            if sp >= 0:
                out.append(p)
            if sp * sq < 0:
                out.append(p + (q - p) * sp / (sp - sq))
    return np.array(out)


def phi(V: Arr) -> float:
    A, c = area_centroid(V)
    I = clip(V, 2 * c - V)
    return area_centroid(I)[0] / A if len(I) >= 3 else 0.0
