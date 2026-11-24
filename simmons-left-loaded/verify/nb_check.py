"""Exact checks: (a) binomial example n=7, m=3 and n=10, m=3 (extended alpha to q = n-m);
(b) negative binomial NB(r, p = 1 - 1/n), mean M = r(n-1): partial sums S_k >= 0 for k <= M,
using exact rationals (alpha_i = P(X <= M-i) - 1 + P(X <= M+i-1))."""
from fractions import Fraction as F
from math import comb

def binom_alpha(n, m):
    p = F(m, n); pmf = [comb(n, j) * p**j * (1 - p)**(n - j) for j in range(n + 1)]
    cdf = lambda x: sum(pmf[:x + 1]) if x >= 0 else F(0)
    q = n - m
    return [cdf(m - i) - (1 - cdf(m + i - 1)) for i in range(1, q + 1)]

for n, m in [(7, 3), (10, 3)]:
    al = binom_alpha(n, m); D = n**n
    S = [sum(al[:k]) for k in range(1, len(al) + 1)]
    print(n, m, "alpha*n^n:", [int(a * D) for a in al], "S*n^n:", [int(s * D) for s in S])
    assert S[-1] == 0 and all(s > 0 for s in S[:-1])

def nb_alpha(r, n, K):
    p = F(n - 1, n); qq = 1 - p; M = r * (n - 1)
    pmf = [comb(k + r - 1, r - 1) * p**k * qq**r for k in range(2 * M + K + 2)]
    assert sum(k * x for k, x in enumerate(pmf)) <= M
    cdf = lambda x: sum(pmf[:x + 1]) if x >= 0 else F(0)
    return M, [cdf(M - i) - (1 - cdf(M + i - 1)) for i in range(1, M + 1)]

bad = 0
for r in range(1, 7):
    for n in range(2, 8):
        M, al = nb_alpha(r, n, 0)
        S = [sum(al[:k]) for k in range(1, M + 1)]
        sg = [a > 0 for a in al if a != 0]
        ch = sum(1 for i in range(len(sg) - 1) if sg[i] != sg[i + 1])
        if min(S) < 0 or ch > 1 or (sg and not sg[0] and ch): bad += 1; print("FAIL", r, n)
print("NB(r, 1-1/n), r<=6, n<=7: failures", bad)
assert bad == 0
