"""Stanley's g(n) = #{w in S_n : D(w) = D(w^-1) = {1,3,5,...}} (OEIS A007999).
(1) brute force small n; (2) exact coefficients of (*):
    sum g(n) x^n = sum_k E_{2k+1}^2 u^{2k+1}/(2k+1)! + (1-x^2)^(-1/2) sum_k E_{2k}^2 u^{2k}/(2k)!,
    u = artanh x;  (3) ratio g(n) / (E_n^2/n!) and n*(ratio-1) vs pi^4/48."""
import itertools
from fractions import Fraction as Fr
from math import comb, factorial, pi

N = 160

# Euler (zigzag) numbers E_n: sec + tan
E = [0] * (N + 1)
A = [[0] * (N + 2) for _ in range(N + 2)]  # Seidel-Entringer
A[0][0] = 1
for n in range(1, N + 1):
    for k in range(1, n + 1):
        A[n][k] = A[n][k - 1] + A[n - 1][n - k]
E = [A[n][n] for n in range(N + 1)]


def polymul(a, b):
    out = [Fr(0)] * (N + 1)
    for i, x in enumerate(a):
        if x:
            for j, y in enumerate(b[: N + 1 - i]):
                if y: out[i + j] += x * y
    return out


u = [Fr(0)] * (N + 1)
for j in range(1, N + 1, 2): u[j] = Fr(1, j)
sq = [Fr(0)] * (N + 1)  # (1-x^2)^(-1/2)
for j in range(0, N + 1, 2): sq[j] = Fr(comb(j, j // 2), 4 ** (j // 2))
odd_part = [Fr(0)] * (N + 1); even_part = [Fr(0)] * (N + 1)
upow = [Fr(1)] + [Fr(0)] * N
for m in range(0, N + 1):
    c = Fr(E[m] ** 2, factorial(m))
    tgt = odd_part if m % 2 else even_part
    for i, v in enumerate(upow):
        if v: tgt[i] += c * v
    upow = polymul(upow, u)
gs = [odd_part[n] + x for n, x in enumerate(polymul(sq, even_part))]
assert all(g.denominator == 1 for g in gs), "non-integer coefficient"
g = [int(x) for x in gs]
print("g(0..12) from (*):", g[:13])


def brute(n):
    S = {i for i in range(1, n) if i % 2 == 1}
    cnt = 0
    for w in itertools.permutations(range(n)):
        inv = [0] * n
        for i, v in enumerate(w): inv[v] = i
        if {i + 1 for i in range(n - 1) if w[i] > w[i + 1]} == S and {i + 1 for i in range(n - 1) if inv[i] > inv[i + 1]} == S:
            cnt += 1
    return cnt


print("brute  (0..9):     ", [1] + [brute(n) for n in range(1, 10)])
print("pi^4/48 =", pi ** 4 / 48)
for n in [10, 20, 40, 80, 120, 159, 160]:
    r = Fr(g[n] * factorial(n), E[n] ** 2)
    print(f"n={n:4d} ratio={float(r):.10f}  n*(ratio-1)={float(n * (r - 1)):.6f}")
