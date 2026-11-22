"""Check the additional monotonicity, two-bias and truncation results.

The derivative certificate is checked as an exact bivariate polynomial identity.
The analytic series transformations and truncation intervals are also checked at
high precision, including coincident, complementary and fair biases. The paper
contains the proofs; these computations are independent consistency checks.
"""
from fractions import Fraction

from mpmath import mp

mp.dps = 60


# Polynomials in the formal variables A and s, with integer coefficients.
def add(*polys):
    out = {}
    for poly in polys:
        for powers, coefficient in poly.items():
            out[powers] = out.get(powers, 0) + coefficient
    return {powers: coefficient for powers, coefficient in out.items() if coefficient}


def scale(poly, coefficient):
    return {powers: coefficient * value for powers, value in poly.items() if coefficient * value}


def mul(left, right):
    terms = []
    for (a, b), x in left.items():
        for (c, d), y in right.items():
            terms.append({(a + c, b + d): x * y})
    return add(*terms)


def ds(poly):
    return {(a, b - 1): b * x for (a, b), x in poly.items() if b}


one, A, s = {(0, 0): 1}, {(1, 0): 1}, {(0, 1): 1}
one_minus_s = add(one, scale(s, -1))
A_minus_s = add(A, scale(s, -1))
A_minus_one = add(A, scale(one, -1))
numerator = mul(one_minus_s, add(mul(A, add(one, s)), scale(mul(s, s), -2)))
derivative_numerator = add(mul(ds(numerator), A_minus_s), scale(numerator, 2))
H = add(mul(A, add(A, scale(one, -2))),
        mul(A, mul(one_minus_s, add(one, scale(s, 2)))), mul(s, mul(s, s)))
certificate = add(mul(A_minus_one, derivative_numerator),
                  scale(mul(s, mul(A_minus_s, mul(A_minus_s, A_minus_s))), 2),
                  scale(mul(one_minus_s, H), -2))
assert not certificate, certificate
print("Exact derivative certificate: all polynomial coefficients vanish")


def density(p):
    if p == mp.mpf(1) / 2:
        return (mp.pi**2 - 9) / 12
    q, r = 1 - p, p * (1 - p)
    return (2 * r - mp.mpf(5) / 4
            + mp.pi**2 * r**2 / 6 * (2 + 3 / mp.sin(mp.pi * p)**2)
            + mp.pi * r * (1 - 3 * r) * mp.cot(mp.pi * p) / (1 - 2 * p))


def F(t):
    return density((1 - mp.sqrt(t)) / 2)


for value in ("0", "0.01", "0.1", "0.5", "0.9", "0.99"):
    t = mp.mpf(value)
    series = (-mp.mpf(1) / 4 + t / 2 + mp.pi**2 * (1 - t)**2 / 48
              + mp.nsum(lambda j: (1 - t) * ((2 * j + 1)**2 * (1 + t) - 2 * t**2)
                        / ((2 * j + 1)**2 - t)**2, [1, mp.inf]) / 2)
    assert abs(series - F(t)) < mp.mpf("1e-45"), value
    stability = (12 - mp.pi**2) * t / 24 + (mp.pi**2 - 6) * t**2 / 48
    assert F(t) - F(0) >= stability - mp.mpf("1e-50"), value
    if t:
        lower = (12 - mp.pi**2) * (1 - t) / 24 + t / 4
        assert mp.diff(F, t) > lower > 0, value
print("Rational series, derivative bound and quantitative minimum: all checks pass")


def G(x):
    return mp.pi * mp.cot(mp.pi * x) - 1 / x


def U(x):
    return -G(x) / x


def V(x, y):
    return (mp.pi**2 * mp.sinc(mp.pi * (y - x))
            / (mp.sin(mp.pi * x) * mp.sin(mp.pi * y)) - 1 / (x * y))


def joint(p1, p2):
    a, b = (p1, 1 - p1), (p2, 1 - p2)
    return (p1 * (1 - p1) * p2 * (1 - p2) / 4
            * (4 * mp.pi**2 / 3 - 2 * sum(U(x) for x in a + b)
               + sum(V(x, y) for x in a for y in b)))


def X(k, p):
    q, r, j = 1 - p, p * (1 - p), k // 2
    if k % 2 == 0:
        return r / (j + 1) * (p / (j + q) + q / (j + p))
    return r / (j + 1) * (q / (j + 1 + q) + p / (j + 1 + p))


def real(x):
    return mp.mpf(x.numerator) / x.denominator


for left, right in (("0.5", "0.5"), ("0.3", "0.7"), ("0.5", "0.2"),
                    ("0.01", "0.99"), ("0.01", "0.01"), ("0.45", "0.45")):
    a, b = Fraction(left), Fraction(right)
    p1, p2 = real(a), real(b)
    value = joint(p1, p2)
    infinite = mp.nsum(lambda j: (X(2 * int(j), p1) * X(2 * int(j), p2)
                                 + X(2 * int(j) + 1, p1) * X(2 * int(j) + 1, p2)) / 4,
                       [0, mp.inf])
    assert abs(infinite - value) < mp.mpf("1e-40"), (left, right)
    if a == b or a + b == 1:
        assert abs(value - density(p1)) < mp.mpf("1e-40"), (left, right)
    for N in (10, 30):
        # These finite sums and error bounds use exact rational arithmetic.
        partial = sum(X(k, a) * X(k, b) for k in range(2 * N + 2)) / 4
        bound = a * (1 - a) * b * (1 - b) / (6 * N**3)
        assert real(partial) < value < real(partial + bound), (left, right, N)
        assert bound <= Fraction(1, 96 * N**3)
    print(f"p1={left}, p2={right}: joint formula and exact-rational truncation intervals pass")
