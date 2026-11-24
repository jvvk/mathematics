"""Lemma 3.2 and Proposition 3.1 checks.

1. Exact (sympy): with s = e^{-theta/8}, (r(1/2) - r(1/4)) - 2(r(1/4) - r(1/8)) equals the factored rational function
   printed in the paper.
2. Numerical: the closed form of Proposition 3.1 agrees with 1 - int_0^1 dC/du dv (finite differences + quadrature).
Exits nonzero on any mismatch.
"""
import sys
import numpy as np
import sympy as sp
from scipy import integrate

s = sp.symbols("s", positive=True)


def R(k: int) -> sp.Expr:  # u = k/8, w = s^k, e^{-theta} = s^8
    w = s**k; x = w - 1; a = s**8 - 1; u = sp.Rational(k, 8)
    return 1 - w * (x - a * u) / (x * (x - a))


defect = (R(4) - R(2)) - 2 * (R(2) - R(1))
paper = -s * (s - 1)**3 * (s + 1) * (s**4 + s**3 + 3 * s**2 + s + 1) / (
    4 * (s**2 - s + 1) * (s**2 + s + 1) * (s**6 + s**5 + s**4 + s**3 + s**2 + s + 1))
ok1 = sp.simplify(sp.together(defect - paper)) == 0
print("Lemma 3.2 identity:", "OK" if ok1 else "MISMATCH")


def C(u, v, t):
    return -np.log1p(np.expm1(-t * u) * np.expm1(-t * v) / np.expm1(-t)) / t


def r_closed(u, t):
    x = np.exp(-t * u) - 1; a = np.exp(-t) - 1
    return 1 - np.exp(-t * u) * (x - a * u) / (x * (x - a))


def r_quad(u, t, h=1e-6):
    return 1 - integrate.quad(lambda v: (C(u + h, v, t) - C(u - h, v, t)) / (2 * h), 0, 1, epsabs=1e-12, limit=200)[0]


worst = max(abs(r_closed(u, t) - r_quad(u, t)) for t in [0.3, 1, 3, 10, -2, -7] for u in np.linspace(0.01, 0.99, 25))
ok2 = worst < 1e-7
print(f"Proposition 3.1 closed form vs quadrature: max error {worst:.1e}", "OK" if ok2 else "MISMATCH")
sys.exit(0 if ok1 and ok2 else 1)
