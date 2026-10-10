"""Assert every number stated in "Raising the apex raises the Gaussian centroid", then reject mutants.

* Section 1: A=(10,0), B=(11,0), apex (0,h): mean heights about 5.050 (h=10) and 4.048 (h=20).
* Remark after Lemma 2: for F(s) = s exp(50 s^2) the derivative of log r at h1=1, h2=2, y=4/5 is exactly -35/6.
* Figure 1: base [-1.2, 0.8], Gaussian centred at (0.5, 0.6), apex heights 0.7, 1.2, 2: centroid heights
  0.251, 0.424, 0.652, recomputed here by Gauss-Legendre quadrature (the figure used adaptive quadrature).

    timeout 300 nice -n 15 ~/.venvs/main/bin/python check.py
"""
from __future__ import annotations

import sys

import numpy as np
import sympy as sp


def centroid_height(a: float, b: float, apex: tuple[float, float], mu=(0.0, 0.0), n: int = 200) -> float:
    """Gaussian mean height of the triangle (a,0), (b,0), apex, by Gauss-Legendre on the map (u,v) -> triangle."""
    x, w = np.polynomial.legendre.leggauss(n)
    t, wt = (x + 1) / 2, w / 2
    U, V = np.meshgrid(t, t, indexing="ij")
    W = np.outer(wt, wt)
    # collapsed square: point = P0 + u (P1 - P0) + u v (P2 - P1), Jacobian u * |det|
    P0, P1, P2 = np.array([a, 0.0]), np.array([b, 0.0]), np.array(apex)
    X = P0[0] + U * (P1[0] - P0[0]) + U * V * (P2[0] - P1[0])
    Y = P0[1] + U * (P1[1] - P0[1]) + U * V * (P2[1] - P1[1])
    J = U
    g = np.exp(-((X - mu[0]) ** 2 + (Y - mu[1]) ** 2) / 2) * J * W
    return float((g * Y).sum() / g.sum())


def run(fig=(0.251, 0.424, 0.652), outside=(5.050, 4.048), slope=sp.Rational(-35, 6), F_exp=50) -> int:
    n = 0
    y10 = centroid_height(10, 11, (0, 10))
    y20 = centroid_height(10, 11, (0, 20))
    assert abs(y10 - outside[0]) < 5e-4 and abs(y20 - outside[1]) < 5e-4, (y10, y20)
    n += 1
    s, y, h1, h2 = sp.symbols("s y h1 h2", positive=True)
    logF = sp.log(s * sp.exp(F_exp * s ** 2))
    logr = logF.subs(s, 1 - y / h2) - logF.subs(s, 1 - y / h1)
    d = sp.simplify(sp.diff(logr, y).subs({h1: 1, h2: 2, y: sp.Rational(4, 5)}))
    assert d == slope, d
    n += 1
    hs = (0.7, 1.2, 2.0)
    got = [centroid_height(-1.2, 0.8, (0, h), (0.5, 0.6)) for h in hs]
    assert all(abs(g - f) < 5e-4 for g, f in zip(got, fig)), got
    assert got[0] < got[1] < got[2]
    n += 2
    return n


if __name__ == "__main__":
    print(f"positive: {run()} checks passed", flush=True)
    mutants = {"figure height 0.43 at h = 1.2": dict(fig=(0.251, 0.43, 0.652)),
               "outside heights swapped": dict(outside=(4.048, 5.050)),
               "slope -35/3": dict(slope=sp.Rational(-35, 3)),
               "F = s exp(5 s^2)": dict(F_exp=5)}
    for name, kw in mutants.items():
        try:
            run(**kw)
        except AssertionError as e:
            print(f"rejected mutant: {name} ({str(e)[:60]})", flush=True)
        else:
            sys.exit(f"UNDETECTED MUTANT: {name}")
    print(f"all {len(mutants)} mutants rejected")
