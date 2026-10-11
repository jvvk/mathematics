"""General Yukawa-coupling / instanton machinery for θ-operators  sum_j x^j Q_j(θ)  (Q_0 = θ^4 up to scale).
Frobenius with θ -> θ+ε to order ε^2, mirror map, K(q), instanton numbers."""
from __future__ import annotations
from fractions import Fraction as F
import sympy as sp

T = sp.symbols("T")
E = 3


def smul(a, b):
    return [sum(a[i] * b[k - i] for i in range(k + 1)) for k in range(E)]


def sinv(a):
    r = [F(1) / a[0]] + [F(0)] * (E - 1)
    for k in range(1, E):
        r[k] = -sum(a[i] * r[k - i] for i in range(1, k + 1)) / a[0]
    return r


def poly_eps(Q, n):
    """Q(n + ε) as a truncated ε-series."""
    P = sp.Poly(sp.expand(Q.subs(T, T + n)), T)
    return [F(int(sp.Rational(P.coeff_monomial(T**k)).p), int(sp.Rational(P.coeff_monomial(T**k)).q)) for k in range(E)]


def frob(Qs, M):
    a = [[F(1)] + [F(0)] * (E - 1)]
    for n in range(1, M + 1):
        rhs = [F(0)] * E
        for j in range(1, len(Qs)):
            if n - j >= 0:
                t = smul(poly_eps(Qs[j], n - j), a[n - j])
                rhs = [rhs[k] - t[k] for k in range(E)]
        a.append(smul(rhs, sinv(poly_eps(Qs[0], n))))
    return a


def pmul(a, b, M):
    return [sum(a[i] * b[k - i] for i in range(k + 1)) for k in range(M + 1)]


def pinv(a, M):
    r = [F(1) / a[0]] + [F(0)] * M
    for k in range(1, M + 1):
        r[k] = -sum(a[i] * r[k - i] for i in range(1, k + 1)) / a[0]
    return r


def pexp(a, M):
    r = [F(1)] + [F(0)] * M
    for k in range(1, M + 1):
        r[k] = sum(j * a[j] * r[k - j] for j in range(1, k + 1)) / k
    return r


def compose(f, g, M):
    r = [F(0)] * (M + 1)
    p = [F(1)] + [F(0)] * M
    for k in range(M + 1):
        r = [r[i] + f[k] * p[i] for i in range(M + 1)]
        p = pmul(p, g, M)
    return r


def revert(q, M):
    x = [F(0), F(1)] + [F(0)] * (M - 1)
    for _ in range(M):
        c = compose(q, x, M)
        x = [x[i] - (c[i] - (1 if i == 1 else 0)) for i in range(M + 1)]
    return x


def yukawa(Qs, M):
    a = frob(Qs, M)
    y0 = [a[n][0] for n in range(M + 1)]
    iy0 = pinv(y0, M)
    g1 = pmul([a[n][1] for n in range(M + 1)], iy0, M)
    g2 = pmul([a[n][2] for n in range(M + 1)], iy0, M)
    h = [g2[k] - pmul(g1, g1, M)[k] / 2 for k in range(M + 1)]
    qx = [F(0)] + pexp(g1, M)[:M]
    hq = compose(h, revert(qx, M), M)
    K = [F(1)] + [k * k * hq[k] for k in range(1, M + 1)]
    return y0, qx, K


def instantons(K, M, w=3):
    n = [F(0)] * (M + 1)
    for m in range(1, M + 1):
        n[m] = (K[m] - sum(n[d] * d ** w for d in range(1, m) if m % d == 0)) / m ** w
    return n


def hadamard_I(R1, R2):
    """L: (n+1)^3 u_{n+1} = R1(n) u_n - R2(n) u_{n-1}, R2 divisible by n.
    Return θ-polys of P = I ⋆ L for v_n = binom(2n,n) u_n:
    (n+1)^4 v_{n+1} = 2(2n+1)R1(n) v_n - 4(2n+1)(2n-1)(R2(n)/n) v_{n-1}.
    In θ-form: Q0(θ)=θ^4, Q1(θ) = -2(2θ+1)R1(θ), Q2(θ) = 4(2θ+3)(2θ+1) (R2/n)(θ+1)."""
    n = sp.symbols("n")
    Q1 = -2 * (2*T + 1) * R1.subs(n, T)
    Q2 = 4 * (2*T + 3) * (2*T + 1) * sp.cancel(R2 / n).subs(n, T + 1)
    return [T**4, sp.expand(Q1), sp.expand(Q2)]
