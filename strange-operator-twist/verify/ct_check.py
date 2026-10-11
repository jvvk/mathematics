"""Pólya 'auxiliary problem, constructed not searched'. Claim: with h(Y) = Y + 2 + 1/Y,
  sum_n u_n s^n = CT_{a,b,Y} 1/(1 - 4 s h(Y) (1 + a + b) + (s^2/4) h(Y)/(a b))  (as formal series in s),
and hence y0(P) = CT_{a,b,Y,Z} 1/(1 - 4 t h(Z) h(Y)(1 + a + b) + (t^2/4) h(Z)^2 h(Y)/(a b)).
Check both against the recurrences, n <= N."""
from collections import defaultdict
from fractions import Fraction as Fr
from math import comb

N = 9


def laurent_mul(p, q):
    r = defaultdict(Fr)
    for k1, v1 in p.items():
        for k2, v2 in q.items():
            r[tuple(a + b for a, b in zip(k1, k2))] += v1 * v2
    return {k: v for k, v in r.items() if v}


def ct_series(A, B, dim):
    """coefficients c_n = CT of [s^n] 1/(1 - s A + s^2 B) = sum_k binom(n-k,k) (-1)^k A^{n-2k} B^k."""
    zero = tuple([0] * dim)
    Apow, Bpow = [{zero: Fr(1)}], [{zero: Fr(1)}]
    for _ in range(N):
        Apow.append(laurent_mul(Apow[-1], A)); Bpow.append(laurent_mul(Bpow[-1], B))
    out = []
    for n in range(N + 1):
        tot = Fr(0)
        for k in range(n // 2 + 1):
            prod = laurent_mul(Apow[n - 2 * k], Bpow[k])
            tot += comb(n - k, k) * (-1) ** k * prod.get(zero, 0)
        out.append(tot)
    return out


# variables (a, b, Y)
h = {(0, 0, 1): Fr(1), (0, 0, 0): Fr(2), (0, 0, -1): Fr(1)}
A = laurent_mul({k: 4 * v for k, v in h.items()}, {(0, 0, 0): Fr(1), (1, 0, 0): Fr(1), (0, 1, 0): Fr(1)})
B = laurent_mul({(-1, -1, 0): Fr(1, 4)}, h)
u = [1, 8]
for n in range(1, N):
    u.append((4*(2*n+1)*(5*n*n+5*n+2)*u[n] - 48*n*(9*n*n-1)*u[n-1]) // (n+1)**3)
got = ct_series(A, B, 3)
print("u_n  from recurrence:", u)
print("u_n  from CT        :", [int(v) if v.denominator == 1 else str(v) for v in got])
