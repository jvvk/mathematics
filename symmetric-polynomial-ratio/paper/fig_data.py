"""Coordinates for Figure 1: f = P_{l-1}/P_l for n = 6, l = 3, x = 2, and the zeros of P_3."""
from math import comb, factorial

import sympy as sp

n, l, x = 6, 3, sp.Integer(2)
t = sp.symbols("t")
y = x - 1


def P(L: int) -> sp.Expr:
    return sp.expand(sum(comb(n + L - 1, L - k) * sp.rf(t, k) / factorial(k) * y**k for k in range(L + 1)))


zeros = sorted(float(r) for r in sp.Poly(P(l), t).nroots())
print("zeros of P_3:", [round(z, 3) for z in zeros])
f = sp.lambdify(t, P(l - 1) / P(l))
start = round(zeros[-1] + 0.45, 1)
pts = [start + k * 0.1 for k in range(int((6 - start) / 0.1) + 1)] + [6.0]
print(" ".join(f"({u:.2f},{f(u):.4f})" for u in pts))
print("f at 0..6:", [round(float(f(k)), 4) for k in range(7)])
