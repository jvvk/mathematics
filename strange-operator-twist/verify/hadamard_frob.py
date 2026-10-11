"""Frobenius basis of P = I ⋆ L from L's θ-operator: A_n(ε) = a_n^L(ε) * prod_{i<=n} 2(2i-1+2ε)/(i+ε).
Then mirror map, Yukawa K(q) as in cyk."""
import sys
from fractions import Fraction as F
import cyk


def frob_P(Qs_L, M):
    a = cyk.frob(Qs_L, M)
    out, b = [], [F(1)] + [F(0)] * (cyk.E - 1)
    for n in range(M + 1):
        if n >= 1:
            num = [F(2 * (2 * n - 1)), F(4)] + [F(0)] * (cyk.E - 2)      # 2(2n-1+2ε)
            den = [F(n), F(1)] + [F(0)] * (cyk.E - 2)                   # n+ε
            b = cyk.smul(b, cyk.smul(num, cyk.sinv(den)))
        out.append(cyk.smul(a[n], b))
    return out


def yukawa_P(Qs_L, M):
    a = frob_P(Qs_L, M)
    y0 = [a[n][0] for n in range(M + 1)]
    iy0 = cyk.pinv(y0, M)
    g1 = cyk.pmul([a[n][1] for n in range(M + 1)], iy0, M)
    g2 = cyk.pmul([a[n][2] for n in range(M + 1)], iy0, M)
    h = [g2[k] - cyk.pmul(g1, g1, M)[k] / 2 for k in range(M + 1)]
    qx = [F(0)] + cyk.pexp(g1, M)[:M]
    hq = cyk.compose(h, cyk.revert(qx, M), M)
    return y0, qx, [F(1)] + [k * k * hq[k] for k in range(1, M + 1)]


if __name__ == "__main__":
    T = cyk.T
    L = [T**3, -4*(2*T+1)*(5*T**2+5*T+2), 48*(T+1)*(3*T+2)*(3*T+4)]
    y0, q, K = yukawa_P(L, 8)
    print("Bogner via Hadamard-Frobenius: y0", [str(v) for v in y0[:5]], "\n q", [str(v) for v in q[:5]], "\n K", [str(v) for v in K[:6]])
