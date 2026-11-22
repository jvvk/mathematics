"""Theorem 1.1: the series (1/4) sum_k X_k(p)^2 against the closed form, two independent ways.

(a) X_k summed directly over Dyck paths of height exactly k by dynamic programming (no continuants,
    no closed forms), truncated; agreement to 1e-6.
(b) X_k from Proposition 4.5, summed with mpmath to 25 digits; agreement to 1e-15.
"""
from collections import defaultdict

from mpmath import cot, csc, inf, mp, mpf, nsum, pi

mp.dps = 30


def closed(p):  # the formula as printed in Theorem 1.1
    q = 1 - p
    r = p * q
    return 2 * r - mpf(5) / 4 + pi**2 * r**2 / 6 * (2 + 3 * csc(pi * p) ** 2) + pi * r * (1 - 3 * r) * cot(pi * p) / (1 - 2 * p)


def X_dp(k, p, N):
    """sum over Dyck paths P of height k, semilength <= N, of u^(1+od) v^ev + v^(1+od) u^ev."""
    u, v = p * p, (1 - p) ** 2
    tot = 0.0
    for s, t, pre in ((v, u, u), (u, v, v)):
        dp = {(0, k == 0): 1.0}
        acc = 1.0 if k == 0 else 0.0
        for step in range(2 * N):
            nd = defaultdict(float)
            for (h, hit), w in dp.items():
                if h < k:
                    nd[(h + 1, hit or h + 1 == k)] += w * (s if h % 2 == 0 else t)
                if h > 0:
                    nd[(h - 1, hit)] += w
            dp = nd
            if step % 2 == 1:
                acc += dp.get((0, True), 0.0)
        tot += pre * acc
    return tot


def X_formula(k, p):
    q, r, j = 1 - p, p * (1 - p), k // 2
    if k % 2 == 0:
        return r / (j + 1) * (p / (j + q) + q / (j + p))
    return r / (j + 1) * (q / (j + 1 + q) + p / (j + 1 + p))


for ps in ["0.1", "0.3", "0.45", "0.7"]:
    p = mpf(ps)
    a = sum(X_dp(k, float(p), 1500) ** 2 for k in range(60)) / 4
    b = nsum(lambda j: (X_formula(2 * int(j), p) ** 2 + X_formula(2 * int(j) + 1, p) ** 2) / 4, [0, inf])
    c = closed(p)
    assert abs(a - float(c)) < 1e-6, (ps, a, c)
    assert abs(b - c) < mpf(10) ** -15, (ps, b, c)
    print(f"p = {ps}: DP {a:.10f}  series {mp.nstr(b, 18)}  closed {mp.nstr(c, 18)}")
half = nsum(lambda j: (X_formula(2 * int(j), mpf(1) / 2) ** 2 + X_formula(2 * int(j) + 1, mpf(1) / 2) ** 2) / 4, [0, inf])
assert abs(half - (pi**2 - 9) / 12) < mpf(10) ** -15
print("p = 1/2:", mp.nstr(half, 18), "= (pi^2 - 9)/12")
