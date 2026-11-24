"""Exact checks of every identity in the paper (sympy) and of the introduction's numbers."""
import sympy as sp
from fractions import Fraction as F
from math import comb
i, m, q, n, r = sp.symbols('i m q n r', positive=True)
t = i * (i + 1)
# binomial ratio (Lemma 3.3)
R = m**2 * (q - i) * (q + i + 1) / (q**2 * (m - i) * (m + i + 1))
assert sp.simplify(R - 1 - (q - m) * ((q + m) * t - m * q) / (q**2 * (m - i) * (m + i + 1))) == 0
# Poisson ratio
assert sp.simplify(m**2 - (m - i) * (m + i + 1) - (t - m)) == 0
# negative binomial: pi = 1 - 1/n, M = r(n-1)
pi = 1 - 1 / n; M = r * (n - 1)
Rnb = pi**2 * (M + i + r) * (M - i + r - 1) / ((M + i + 1) * (M - i))
assert sp.simplify(Rnb - 1 - (2 * n - 1) * (t - M * n) / (n**2 * (M - i) * (M + i + 1))) == 0
assert sp.simplify(r * pi / (1 - pi) - M) == 0
# direct check of beta ratio for NB from the pmf, small cases
def nbp(k, rr, nn): return comb(k + rr - 1, rr - 1) * F(nn - 1, nn)**k * F(1, nn)**rr
for rr in range(1, 5):
    for nn in range(2, 6):
        MM = rr * (nn - 1)
        for ii in range(0, MM):
            b = lambda j: nbp(MM + j, rr, nn) / nbp(MM - j, rr, nn)
            lhs = b(ii + 1) / b(ii) - 1
            rhs = F((2 * nn - 1) * (ii * (ii + 1) - MM * nn), nn**2 * (MM - ii) * (MM + ii + 1))
            assert lhs == rhs, (rr, nn, ii)
# introduction: Bin(7, 3/7)
p = F(3, 7); pm = [comb(7, j) * p**j * (1 - p)**(7 - j) for j in range(8)]
vals = [sum(pm[:3]), sum(pm[4:]), sum(pm[:2]), sum(pm[5:])]
print([round(float(v), 4) for v in vals])
assert [round(float(v), 4) for v in vals] == [0.3593, 0.3469, 0.1243, 0.1266]
print("all identities verified")
