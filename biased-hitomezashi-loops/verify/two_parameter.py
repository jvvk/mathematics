"""Theorem 6.2: the two-bias density (1/4) sum_k X_k(p1) X_k(p2) against its cot/csc^2 closed form,
c = (r1 r2 / 4) sum_{m != 0} A1(m) A2(m), A(m) = 2/m - 1/(m+p) - 1/(m+q), evaluated with the
classical sums over m in Z \\ {0}.  Agreement to 1e-15 at five pairs, including fair and complementary biases.
"""
from mpmath import inf, mp, mpf, nsum, pi, cot, sin, sinc

mp.dps = 30
C = lambda x: pi * cot(pi * x)


def S_mx(x):  # sum_{m != 0} 1/(m(m+x))
    return (1 / x) * (1 / x - C(x))


def S_xy(x, y):  # sum_{m != 0} 1/((m+x)(m+y))
    return pi**2 * sinc(pi * (y - x)) / (sin(pi * x) * sin(pi * y)) - 1 / (x * y)


def closed(p1, p2):
    q1, q2 = 1 - p1, 1 - p2
    tot = 4 * pi**2 / 3 - 2 * (S_mx(p2) + S_mx(q2)) - 2 * (S_mx(p1) + S_mx(q1))
    tot += sum(S_xy(x, y) for x in (p1, q1) for y in (p2, q2))
    return p1 * q1 * p2 * q2 / 4 * tot


def X(k, p):
    q, r, j = 1 - p, p * (1 - p), k // 2
    if k % 2 == 0:
        return r / (j + 1) * (p / (j + q) + q / (j + p))
    return r / (j + 1) * (q / (j + 1 + q) + p / (j + 1 + p))


for a, b in [("0.3", "0.3"), ("0.2", "0.45"), ("0.1", "0.7"), ("0.5", "0.5"), ("0.3", "0.7")]:
    p1, p2 = mpf(a), mpf(b)
    s = nsum(lambda j: (X(2 * int(j), p1) * X(2 * int(j), p2) + X(2 * int(j) + 1, p1) * X(2 * int(j) + 1, p2)) / 4, [0, inf])
    c = closed(p1, p2)
    assert abs(s - c) < mpf(10) ** -15, (a, b, s, c)
    print(f"p1 = {a}, p2 = {b}: series {mp.nstr(s, 18)}  closed {mp.nstr(c, 18)}")
