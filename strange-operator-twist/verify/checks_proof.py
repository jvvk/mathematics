"""(1) Self-duality of P in BV's form: 2 V2 + θ_q V3 = 0, with y_i/y0 in the q-coordinate.
(2) c_p = zeta * (-4)^((p-1)/4) for a 4th root of unity zeta, i.e. c_p^4 ≡ (-4)^(p-1) mod p^3 and c_p ≡ 1 mod p."""
from fractions import Fraction as F
import cyk
import sympy as sp

T = cyk.T
cyk.E = 4
M = 16
Qs = [T**4, -8*(2*T+1)**2*(5*T**2+5*T+2), 192*(2*T+1)*(3*T+2)*(3*T+4)*(2*T+3)]
a = cyk.frob(Qs, M)
Fi = [[a[n][i] for n in range(M+1)] for i in range(4)]
iy0 = cyk.pinv(Fi[0], M)
g = [cyk.pmul(Fi[i], iy0, M) for i in range(4)]        # F_i/F_0, i = 1..3
# y_i/y0 = sum_{j} g_j L^{i-j}/(i-j)!, L = log x; t = log q = L + g1.
# V2 = g2 - g1^2/2 ; V3 = g3 - g1 g2 + g1^3/3  (y3/y0 = t^3/6 + V2 t + V3)
g1, g2, g3 = g[1], g[2], g[3]
mul = lambda u, v: cyk.pmul(u, v, M)
V2 = [g2[k] - mul(g1, g1)[k] / 2 for k in range(M+1)]
V3 = [g3[k] - mul(g1, g2)[k] + mul(g1, mul(g1, g1))[k] / 3 for k in range(M+1)]
qx = [F(0)] + cyk.pexp(g1, M)[:M]
xq = cyk.revert(qx, M)
V2q, V3q = cyk.compose(V2, xq, M), cyk.compose(V3, xq, M)
res = [2*V2q[k] + k*V3q[k] for k in range(M+1)]
print("self-duality 2V2 + θV3 = 0 through q^%d:" % M, all(r == 0 for r in res))

bad = []
for p in sp.primerange(3, 200):
    c = sp.legendre_symbol(2, p) * 2**((p-1)//2)
    m = p**3
    if (c % p != 1) or (pow(c, 4, m) - pow(-4, p-1, m)) % m:
        bad.append(p)
print("c_p ≡ 1 (mod p) and c_p^4 ≡ (-4)^(p-1) (mod p^3) for all odd p < 200:", not bad, bad[:5])
