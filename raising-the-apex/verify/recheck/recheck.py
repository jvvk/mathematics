"""Independent recheck of "Raising the apex raises the Gaussian centroid", sharing no code with verify.py or
check.py: Monte Carlo on actual Gaussian points. Sample standard Gaussian points (shifted), keep those inside the
pyramid, and average their heights. Checks: the centroid heights of Figure 1 (within 5 standard errors), strict
rise with the apex for triangles with feet at both ends and inside the base and for a tetrahedron over a
non-symmetric triangular base, and the fall in the foot-outside example. Seeded; numpy only.

    timeout 900 nice -n 15 ~/.venvs/main/bin/python recheck.py
"""
from __future__ import annotations

import sys

import numpy as np

rng = np.random.default_rng(499635)
N = 4_000_000


def heights_in_triangle(a: float, b: float, d: float, h: float, mu) -> np.ndarray:
    """Heights of Gaussian points (centred at mu) inside the triangle (a,0),(b,0),(d,h)."""
    P = rng.standard_normal((N, 2)) + np.asarray(mu)
    x, y = P[:, 0], P[:, 1]
    inside = (y > 0) & (y < h) & (x > a + (d - a) * y / h) & (x < b + (d - b) * y / h)
    return y[inside]


def weighted_height(a: float, b: float, d: float, h: float) -> tuple[float, float]:
    """Far from the Gaussian's centre: uniform points in the triangle, weighted by the Gaussian density
    (self-normalised; the weights are rescaled by their maximum, so no underflow)."""
    u, v = rng.random(N), rng.random(N)
    r = np.sqrt(u)
    P0, P1, P2 = np.array([a, 0.0]), np.array([b, 0.0]), np.array([d, h])
    pts = (1 - r)[:, None] * P0 + (r * (1 - v))[:, None] * P1 + (r * v)[:, None] * P2
    logw = -(pts ** 2).sum(1) / 2
    w = np.exp(logw - logw.max())
    m = float((w * pts[:, 1]).sum() / w.sum())
    neff = w.sum() ** 2 / (w ** 2).sum()
    se = float(np.sqrt(((w * (pts[:, 1] - m) ** 2).sum() / w.sum()) / neff))
    return m, se


def mean_se(v: np.ndarray) -> tuple[float, float]:
    return float(v.mean()), float(v.std() / np.sqrt(len(v)))


def run(fig=(0.251, 0.424, 0.652), outside_falls: bool = True, monotone_sign: int = 1) -> int:
    n = 0
    prev = -np.inf
    for h, f in zip((0.7, 1.2, 2.0), fig):
        m, se = mean_se(heights_in_triangle(-1.2, 0.8, 0.0, h, (0.5, 0.6)))
        assert abs(m - f) < 5 * se + 5e-4, (h, m, f, se)
        assert monotone_sign * (m - prev) > 0, (h, m, prev)
        prev = m
        n += 2
        print(f"figure: h={h}: mean height {m:.4f} +- {se:.4f} (stated {f})", flush=True)
    # feet at an end and inside, Gaussian centred off to one side
    for d, mu in ((-1.0, (2.0, -0.5)), (0.3, (-1.5, 1.0)), (1.0, (0.0, 0.0))):
        ms = [mean_se(heights_in_triangle(-1.0, 1.0, d, h, mu)) for h in (0.5, 1.0, 2.0, 4.0)]
        for (m1, s1), (m2, s2) in zip(ms, ms[1:]):
            assert monotone_sign * (m2 - m1) > 5 * np.hypot(s1, s2), (d, mu, ms)
            n += 1
        print(f"foot {d}, centre {mu}: " + ", ".join(f"{m:.3f}" for m, _ in ms), flush=True)
    # tetrahedron over a non-symmetric base in the plane z = 0, foot inside the base
    base = np.array([[-1.0, -0.5], [1.2, -0.3], [0.1, 1.1]])
    foot = 0.2 * base[0] + 0.3 * base[1] + 0.5 * base[2]
    T = np.linalg.inv(np.column_stack([base[1] - base[0], base[2] - base[0]]))
    prevm = -np.inf
    for h in (0.5, 1.0, 2.0):
        P = rng.standard_normal((N, 3)) + np.array([0.4, -0.2, 0.3])
        z = P[:, 2]
        s = 1 - z / h
        ok = (z > 0) & (z < h)
        q = foot + (P[:, :2] - foot) / np.where(ok, s, 1)[:, None]  # point of the base this section point scales from
        lam = (q - base[0]) @ T.T
        inside = ok & (lam[:, 0] >= 0) & (lam[:, 1] >= 0) & (lam.sum(1) <= 1)
        m, se = mean_se(z[inside])
        assert monotone_sign * (m - prevm) > 0, (h, m, prevm)
        prevm = m
        n += 1
        print(f"tetrahedron h={h}: mean height {m:.4f} +- {se:.4f}", flush=True)
    # foot outside the base: the mean height falls
    m10, s10 = weighted_height(10.0, 11.0, 0.0, 10.0)
    m20, s20 = weighted_height(10.0, 11.0, 0.0, 20.0)
    assert (m20 < m10 - 5 * np.hypot(s10, s20)) == outside_falls, (m10, m20)
    n += 1
    print(f"foot outside: {m10:.3f} at h=10, {m20:.3f} at h=20", flush=True)
    return n


if __name__ == "__main__":
    print(f"positive: {run()} checks passed\n", flush=True)
    for name, kw in {"figure height 0.40 at h = 1.2": dict(fig=(0.251, 0.40, 0.652)),
                     "foot-outside heights claimed to rise": dict(outside_falls=False),
                     "centroid claimed to fall": dict(monotone_sign=-1)}.items():
        try:
            run(**kw)
        except AssertionError as e:
            print(f"rejected mutant: {name} ({str(e)[:70]})\n", flush=True)
        else:
            sys.exit(f"UNDETECTED MUTANT: {name}")
    print("all 3 mutants rejected")
