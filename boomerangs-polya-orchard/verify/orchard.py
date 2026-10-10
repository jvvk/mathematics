"""Boomerangs in Polya's orchard (MO q/224015).

Discs of radius r sit at every nonzero lattice point. A counterclockwise circular arc of
radius a leaves the origin in direction theta; its point at distance s from the origin has
polar angle theta + arcsin(s / 2a), s in [0, 2a]. The reach of the arc is the largest
distance from the origin it attains before first touching a disc (2a if it survives the
whole half circle). B(r) is the supremum of the reach over a and theta.

Clockwise arcs are mirror images, and rotating by pi/2 maps the lattice to itself, so
counterclockwise arcs with theta in [0, pi/2) cover every case.
"""

from __future__ import annotations

import math

import numpy as np

QUARTER = math.pi / 2


def lattice(dmax: float) -> tuple[np.ndarray, np.ndarray]:
    """Nonzero lattice points with norm <= dmax, sorted by norm."""
    m = int(math.ceil(dmax))
    x, y = np.meshgrid(np.arange(-m, m + 1), np.arange(-m, m + 1))
    x, y = x.ravel(), y.ravel()
    rho = np.hypot(x, y)
    keep = (rho > 0) & (rho <= dmax)
    order = np.argsort(rho[keep], kind="stable")
    return np.stack([x[keep][order], y[keep][order]], axis=1).astype(float), rho[keep][
        order
    ]


def exact_reach(a: float, theta: float, r: float, pts: np.ndarray) -> float:
    """Exact reach of the ccw arc (a, theta); pts must contain every point within reach."""
    c = np.array([-a * math.sin(theta), a * math.cos(theta)])
    d = np.hypot(pts[:, 0] - c[0], pts[:, 1] - c[1])
    hit = np.abs(d - a) < r
    if not hit.any():
        return 2 * a
    q, dq = pts[hit], d[hit]
    phi_q = np.mod(
        np.arctan2(q[:, 1] - c[1], q[:, 0] - c[0]) - (theta - QUARTER), 2 * math.pi
    )
    delta = np.arccos(np.clip((a * a + dq * dq - r * r) / (2 * a * dq), -1.0, 1.0))
    entry = float(np.min(phi_q - delta))
    return 2 * a * math.sin(min(entry, math.pi) / 2)


def _subtract(
    free: list[tuple[float, float]], lo: float, hi: float
) -> list[tuple[float, float]]:
    out = []
    for f0, f1 in free:
        if hi <= f0 or lo >= f1:
            out.append((f0, f1))
            continue
        if f0 < lo:
            out.append((f0, lo))
        if hi < f1:
            out.append((hi, f1))
    return out


def _intervals(a: float, r: float, pts: np.ndarray, rho: np.ndarray, n: int):
    """Exact theta intervals (start mod pi/2, width) blocked by the n nearest discs.

    Disc q (polar rho, alpha) meets the outbound half of the arc iff sin(alpha - theta) lies
    in (L, U), L = (rho^2 - 2ar - r^2) / (2 a rho), U = (rho^2 + 2ar - r^2) / (2 a rho).
    """
    p, rh = pts[:n], rho[:n]
    lo_s = (rh * rh - 2 * a * r - r * r) / (2 * a * rh)
    hi_s = (rh * rh + 2 * a * r - r * r) / (2 * a * rh)
    psi_lo = np.arcsin(np.clip(lo_s, -1.0, 1.0))
    psi_hi = np.where(hi_s >= 1.0, QUARTER + 1e-9, np.arcsin(np.clip(hi_s, -1.0, 1.0)))
    alpha = np.arctan2(p[:, 1], p[:, 0])
    return np.mod(alpha - psi_hi, QUARTER), np.minimum(psi_hi - psi_lo, QUARTER)


def _gaps(lo: np.ndarray, w: np.ndarray) -> list[tuple[float, float]]:
    """Uncovered parts of [0, pi/2) for intervals [lo, lo + w) taken mod pi/2."""
    if len(lo) == 0:
        return [(0.0, QUARTER)]
    hi = lo + w
    wrap = hi > QUARTER
    lo = np.concatenate([lo, np.zeros(int(wrap.sum()))])
    hi = np.concatenate([np.minimum(hi, QUARTER), hi[wrap] - QUARTER])
    order = np.argsort(lo)
    lo, hi = lo[order], hi[order]
    reach = np.maximum.accumulate(hi)
    gaps = []
    if lo[0] > 0:
        gaps.append((0.0, float(lo[0])))
    idx = np.nonzero(lo[1:] > reach[:-1])[0]
    gaps += [(float(reach[i]), float(lo[i + 1])) for i in idx]
    if reach[-1] < QUARTER:
        gaps.append((float(reach[-1]), QUARTER))
    return gaps


def kill_radius(a: float, r: float, pts: np.ndarray, rho: np.ndarray):
    """Distance of the disc whose interval closes the last open direction, and the open
    directions just before it. If an arc survives its whole outbound half the reach is 2a;
    returns inf when that half runs past the discs in pts."""
    n = int(np.searchsorted(rho, 2 * a + r, side="right"))
    lo, w = _intervals(a, r, pts, rho, n)
    if _gaps(lo, w):                   # some arc survives its whole outbound half
        return (2 * a if 2 * a + r <= rho[-1] else math.inf), _gaps(lo, w)
    k0, k1 = 0, n                      # gaps nonempty for first k0, empty for first k1
    while k1 - k0 > 1:
        k = (k0 + k1) // 2
        if _gaps(lo[:k], w[:k]):
            k0 = k
        else:
            k1 = k
    return float(rho[k1 - 1]), _gaps(lo[:k0], w[:k0])


def reach_for_radius(a: float, r: float, pts: np.ndarray, rho: np.ndarray,
                     samples: int = 32) -> tuple[float, float]:
    """Max exact reach over theta for arc radius a (pts must extend past 2a + r or past
    the reach), and a theta attaining it."""
    _, gaps = kill_radius(a, r, pts, rho)
    best, arg = -1.0, 0.0
    for f0, f1 in gaps:
        eps = 1e-12 * max(1.0, f1 - f0)
        for t in np.concatenate([[f0 + eps, f1 - eps], np.linspace(f0, f1, samples)[1:-1]]):
            v = exact_reach(a, float(t), r, pts)
            if v > best:
                best, arg = v, float(t)
    return best, arg


def polish(
    a: float, theta: float, r: float, pts: np.ndarray, iters: int = 4000, seed: int = 0
) -> tuple[float, float, float]:
    """Random local search on the exact reach around (a, theta)."""
    rng = np.random.default_rng(seed)
    best = exact_reach(a, theta, r, pts)
    sa, st = 0.05 * a, 1e-3
    for i in range(iters):
        a2 = a + sa * rng.standard_normal()
        t2 = theta + st * rng.standard_normal()
        if a2 <= 0:
            continue
        v = exact_reach(a2, t2, r, pts)
        if v > best:
            a, theta, best = a2, t2, v
        if i % 500 == 499:
            sa, st = sa * 0.6, st * 0.6
    return best, a, theta
