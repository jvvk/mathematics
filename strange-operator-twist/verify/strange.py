"""Bogner's 'strange operator' (Almkvist-van Straten 2021, arXiv 2103.08651, p.21):
theta^4 - 8x(2θ+1)^2(5θ^2+5θ+2) + 192x^2(2θ+1)(3θ+2)(3θ+4)(2θ+3).
Reproduce y0, q(x), K(q) and instanton numbers n_d by the Frobenius method in exact rationals."""
from __future__ import annotations
from fractions import Fraction as F
import sys

M = int(sys.argv[1]) if len(sys.argv) > 1 else 14   # x-order
E = 3                                                # epsilon order (need eps^0..eps^2)


def smul(a: list[F], b: list[F]) -> list[F]:
    return [sum(a[i] * b[k - i] for i in range(k + 1)) for k in range(E)]


def sinv(a: list[F]) -> list[F]:
    r = [F(1) / a[0]] + [F(0)] * (E - 1)
    for k in range(1, E):
        r[k] = -sum(a[i] * r[k - i] for i in range(1, k + 1)) / a[0]
    return r


def lin(c0: int, c1: int) -> list[F]:   # c0 + c1*eps
    return [F(c0), F(c1)] + [F(0)] * (E - 2)


def prod(*fs: list[F]) -> list[F]:
    r = [F(1)] + [F(0)] * (E - 1)
    for f in fs:
        r = smul(r, f)
    return r


def frob() -> list[list[F]]:
    """a_n(eps) for theta -> theta + eps. Coefficient of x^{n+eps}:
    (n+e)^4 a_n - 8(2(n-1+e)+1)^2(5m^2+5m+2)|_{m=n-1+e} a_{n-1} + 192 P(n-2+e) a_{n-2} = 0."""
    a = [[F(1)] + [F(0)] * (E - 1)]
    for n in range(1, M + 1):
        m1 = lin(n - 1, 1)
        q1 = [x * 5 for x in smul(m1, m1)]
        q1 = [q1[k] + 5 * m1[k] + (2 if k == 0 else 0) for k in range(E)]
        t1 = prod(lin(2 * n - 1, 2), lin(2 * n - 1, 2), q1, [F(8)] + [F(0)] * (E - 1), a[n - 1])
        t2 = [F(0)] * E
        if n >= 2:
            m = n - 2
            t2 = prod(lin(2 * m + 1, 2), lin(3 * m + 2, 3), lin(3 * m + 4, 3), lin(2 * m + 3, 2),
                      [F(192)] + [F(0)] * (E - 1), a[n - 2])
        rhs = [t1[k] - t2[k] for k in range(E)]
        a.append(smul(rhs, sinv(prod(*[lin(n, 1)] * 4))))
    return a


def pmul(a, b):
    return [sum(a[i] * b[k - i] for i in range(k + 1)) for k in range(M + 1)]


def pinv(a):
    r = [F(1) / a[0]] + [F(0)] * M
    for k in range(1, M + 1):
        r[k] = -sum(a[i] * r[k - i] for i in range(1, k + 1)) / a[0]
    return r


def pexp(a):   # a[0] == 0
    r = [F(1)] + [F(0)] * M
    # r' = a' r
    da = [k * a[k] for k in range(M + 1)]
    for k in range(1, M + 1):
        r[k] = sum(da[j] * r[k - j] for j in range(1, k + 1)) / k
    return r


def compose(f, g):   # f(g(x)), g[0] == 0
    r = [F(0)] * (M + 1)
    p = [F(1)] + [F(0)] * M
    for k in range(M + 1):
        r = [r[i] + f[k] * p[i] for i in range(M + 1)]
        p = pmul(p, g)
    return r


def revert(q):   # q = x + ..., return x(q)
    x = [F(0), F(1)] + [F(0)] * (M - 1)
    for _ in range(M):
        c = compose(q, x)
        x = [x[i] - (c[i] - (1 if i == 1 else 0)) for i in range(M + 1)]
    return x


def main() -> tuple[list[F], list[F]]:
    a = frob()
    y0 = [a[n][0] for n in range(M + 1)]
    f1 = [a[n][1] for n in range(M + 1)]
    f2 = [a[n][2] for n in range(M + 1)]
    iy0 = pinv(y0)
    g1, g2 = pmul(f1, iy0), pmul(f2, iy0)
    h = [g2[k] - pmul(g1, g1)[k] / 2 for k in range(M + 1)]
    qx = [F(0)] + pexp(g1)[:M]              # q = x exp(g1)
    xq = revert(qx)
    hq = compose(h, xq)
    K = [F(1) if k == 0 else F(0) for k in range(M + 1)]
    K = [K[k] + k * k * hq[k] for k in range(M + 1)]   # (q d/dq)^2
    print("y0:", [int(v) for v in y0[:6]])
    print("q :", [str(v) for v in qx[:6]])
    print("K :", [str(v) for v in K[:6]])
    return K, qx


def instantons(K: list[F], w: int = 3) -> list[F]:
    """K = 1 + sum_d n_d d^w q^d/(1-q^d)  =>  K_m = sum_{d|m} n_d d^w."""
    n = [F(0)] * (M + 1)
    for m in range(1, M + 1):
        n[m] = (K[m] - sum(n[d] * d ** w for d in range(1, m) if m % d == 0)) / m ** w
    return n


if __name__ == "__main__":
    K, _ = main()
    print("n_d (d^3):", [str(v) for v in instantons(K)[1:9]])
