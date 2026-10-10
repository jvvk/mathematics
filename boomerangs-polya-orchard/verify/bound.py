"""Rigorous upper bound U(r) >= B(r) from the corridor lemma (see NOTES.md).

For a primitive v (length m, direction u mod pi) call v heavy for arc radius a when the
angle eps_v with a(1 - cos eps_v) = 1/m + 2r satisfies tan eps_v < 2r/m. A surviving arc's
second-half direction interval J (length lambda, reach D = 2a sin lambda) contains no
[u, u + eps_v] with v heavy, so lambda < max over cyclically consecutive heavy u_{j-1}, u_j
of (u_j - u_{j-1} + eps_j). Heavy sets grow and eps_v shrinks as a grows, so this bound on
lambda is non-increasing in a and the grid bound 2 a_{i+1} sin(lambda_max(a_i)) covers
[a_i, a_{i+1}]. For a >= 4/r^3 a Minkowski argument gives D < 3/(2r) + r.
"""
from __future__ import annotations

import math
import sys

import numpy as np


def primitive(mmax: float) -> tuple[np.ndarray, np.ndarray]:
    k = int(mmax) + 1
    q, p = np.meshgrid(np.arange(-k, k + 1), np.arange(0, k + 1))
    q, p = q.ravel(), p.ravel()
    keep = ((p > 0) | (q > 0)) & (np.gcd(q, p) == 1) & (np.hypot(q, p) <= mmax)
    q, p = q[keep], p[keep]
    return np.arctan2(p, q).astype(float), np.hypot(q, p)


def lambda_max(a: float, r: float, u: np.ndarray, m: np.ndarray) -> float:
    c = 1 - (1 / m + 2 * r) / a
    ok = c > -1
    eps = np.full_like(m, np.inf)
    eps[ok] = np.arccos(c[ok])
    heavy = ok & (np.tan(np.minimum(eps, 1.5)) < 2 * r / m) & (eps < 1.5)
    if heavy.sum() < 2:
        return math.inf
    uh, eh = u[heavy], eps[heavy]
    order = np.argsort(uh)
    uh, eh = uh[order], eh[order]
    gaps = np.diff(np.concatenate([uh[-1:] - math.pi, uh]))
    return float(np.max(gaps + eh))


def upper(r: float, ratio: float = 1.002) -> tuple[float, float]:
    a1 = 4 / r**3
    u, m = primitive(4 * math.sqrt(a1 * r) + 4)
    best, arg = 1.5 / r + r, a1
    a = 0.5
    while a < a1:
        a_next = min(a * ratio, a1)
        lam = min(lambda_max(a, r, u, m), math.pi / 2)
        bound = 2 * a_next * math.sin(lam)
        if bound > best:
            best, arg = bound, a
        a = a_next
    return best, arg


if __name__ == "__main__":
    for inv in map(float, sys.argv[1:]):
        U, a = upper(1 / inv)
        print(f"1/r={inv:6.0f}  U={U:12.1f}  U*r^2={U/inv**2:.3f}  at a*r^2={a/inv**2:.3f}", flush=True)
