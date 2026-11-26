"""Check the catalytic equation  P(u) = z + (Q(1)-Q(u))/(1-u) + z Q(u),  Q(u) = Y/(1-Y),  Y = t u^2 P(u),
and Q(1) = z * Sum_k t^k B_k(z), against brute force. Series in t truncated at order N; coefficients are
sympy polynomials in u, z."""
import sys as _sys
if not __debug__:
    _sys.exit("refusing to run under python -O: the checks are assertions")
import sympy as sp
from brute import row
u, z = sp.symbols('u z')
N = 9

def mul(a, b):
    c = [sp.Integer(0)] * (N + 1)
    for i, x in enumerate(a):
        if x == 0: continue
        for j in range(N + 1 - i):
            if b[j] != 0: c[i + j] += x * b[j]
    return [sp.expand(e) for e in c]

P = [z] + [sp.Integer(0)] * N
for it in range(N + 1):
    Y = [sp.Integer(0)] + [sp.expand(u**2 * P[i]) for i in range(N)]   # t u^2 P
    Q, Yp = [sp.Integer(0)] * (N + 1), Y
    for _ in range(N):
        Q = [a + b for a, b in zip(Q, Yp)]
        Yp = mul(Yp, Y)
    Q1 = [e.subs(u, 1) for e in Q]
    P = [sp.expand(sp.cancel((Q1[i] - Q[i]) / (1 - u)) + z * Q[i] + (z if i == 0 else 0)) for i in range(N + 1)]
for k in range(1, N + 1):
    Bk = sp.Poly(sp.expand(Q1[k] / z), z).all_coeffs()[::-1]
    assert Bk == row(k), (k, Bk, row(k))
print("catalytic equation reproduces brute-force rows for k <=", N)
