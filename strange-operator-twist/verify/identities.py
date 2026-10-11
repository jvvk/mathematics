"""Verify to high order:
(1) f0 (solution of D) = (1-16x)^(-1/4) 2F1(1/12,5/12;1; z),  z = -6912 x^4/(1-16x)^3
(2) u_n (solution of L) = sum_m (-1)^m 4^(n-3m) (2n-2m)! / (m!^3 (n-m)! (n-4m)!)
(3) y0 of P = binom(2n,n) u_n  (already checked in deep.py; recheck from (2))
(4) j(x) = (16x-1)^3/(4x^4) equals 1/Q + 744 + 196884 Q + ... for Q = -4 x(q_D)^4 + ..."""
from fractions import Fraction as F
from math import comb, factorial as fac

N = 120
# (2) closed form vs recurrence
u = [1, 8]
for n in range(1, N):
    u.append((4*(2*n+1)*(5*n*n+5*n+2)*u[n] - 48*n*(9*n*n-1)*u[n-1]) // (n+1)**3)
cf = [sum((-1)**m * 4**(n-3*m) * fac(2*n-2*m) // (fac(m)**3 * fac(n-m) * fac(n-4*m)) for m in range(n//4 + 1))
      for n in range(N + 1)]
# exactness of the integer division: check each term is an integer
for n in range(N + 1):
    for m in range(n//4 + 1):
        assert (4**(n-3*m) * fac(2*n-2*m)) % (fac(m)**3 * fac(n-m) * fac(n-4*m)) == 0 or 3*m > n
print("(2) closed form for L's u_n matches recurrence to n =", N, ":", cf == u)


def mul(a, b, M):
    return [sum(a[i]*b[k-i] for i in range(k+1)) for k in range(M+1)]


def binom_series(alpha, c, M):   # (1 + c x)^alpha
    r, t = [], F(1)
    for k in range(M+1):
        r.append(t * c**k)
        t = t * (alpha - k) / (k + 1)
    return r


M = 60
# f0 from D's recurrence: (n+1)^2 f_{n+1} = 4(10n^2+5n+1) f_n - 48(3n-2)(3n-1) f_{n-1}
f = [F(1), F(4)]
for n in range(1, M):
    f.append((4*(10*n*n+5*n+1)*f[n] - 48*(3*n-2)*(3*n-1)*f[n-1]) / (n+1)**2)
# RHS: sum_m (1/12)_m (5/12)_m / m!^2 * (-6912)^m x^{4m} (1-16x)^{-3m-1/4}
rhs = [F(0)] * (M+1)
c = F(1)
for m in range(M//4 + 1):
    ser = binom_series(F(-3*m) - F(1, 4), F(-16), M - 4*m)
    for k, v in enumerate(ser):
        rhs[4*m + k] += c * F(-6912)**m * v
    c = c * (F(1, 12) + m) * (F(5, 12) + m) / (m + 1)**2
print("(1) f0 = (1-16x)^(-1/4) 2F1(1/12,5/12;1;z) to x^%d:" % M, f == rhs)
print("(3) y0(P) = binom(2n,n) u_n: first terms", [comb(2*n, n)*u[n] for n in range(6)])
