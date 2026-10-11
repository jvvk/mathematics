"""Mutation tests for the twisted formula: each variant must produce non-integral n_d."""
import json
from fractions import Fraction as F
from sympy import jacobi_symbol, legendre_symbol

K0 = json.load(open("K80.json"))
M = len(K0) - 1


def run(K, w):
    n = [F(0)] * (M + 1)
    for m in range(1, M + 1):
        n[m] = F(K[m] - sum(n[d] * d**3 * w(d, m // d) for d in range(1, m) if m % d == 0), m**3)
    return [d for d in range(1, M + 1) if n[d].denominator != 1]


def make_w(base, chi, sign_power=True):
    def w(d, k):
        if (d * (k - 1)) % 2:
            return 0
        if k % 2 == 0 or (base == 3 and k % 3 == 0):
            return base ** (d * (k - 1) // 2) if d % 2 == 0 else 0
        s = chi(k) ** d if sign_power else chi(k)
        return s * base ** (d * (k - 1) // 2)
    return w


kron2 = lambda k: jacobi_symbol(2, k)
cases = {
    "correct (sqrt2, (2/k)^d)": (K0, make_w(2, kron2)),
    "sqrt3, (3/k)^d": (K0, make_w(3, lambda k: jacobi_symbol(3, k))),
    "sqrt2, no sign": (K0, make_w(2, lambda k: 1)),
    "sqrt2, (-1/k)^d": (K0, make_w(2, lambda k: jacobi_symbol(-1 % k if k > 1 else 1, k) if k > 1 else 1)),
    "sqrt2, (2/k) not ^d": (K0, make_w(2, kron2, sign_power=False)),
    "correct w, K_23 += 23^3": ([v + (23**3 if i == 23 else 0) for i, v in enumerate(K0)], make_w(2, kron2)),
    "correct w, K_45 += 45^2": ([v + (45**2 if i == 45 else 0) for i, v in enumerate(K0)], make_w(2, kron2)),
}
for name, (K, w) in cases.items():
    bad = run(K, w)
    print(f"{name:28s}: {len(bad):2d} non-integral, first {bad[:6]}")
