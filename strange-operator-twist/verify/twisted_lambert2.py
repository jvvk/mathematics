"""Galois-equivariant multicover formula after rescaling by sqrt(2):
K_m = sum_{d | m} n_d d^3 w_d(m/d),  w_d(k) = kron(2,k)^d * 2^{d(k-1)/2}  (terms with d(k-1) odd are 0).
Derivation: Q = sqrt(2) q, K~(Q) = 1 + sum_d d^3 sum_k Frob_k(nu_d) Q^{dk}, nu_d = n_d sqrt(2)^{-d}."""
import json
from fractions import Fraction as F
from sympy import jacobi_symbol

K = json.load(open("K110.json"))
M = len(K) - 1


def w(d, k):
    if (d * (k - 1)) % 2:
        return 0
    if k % 2 == 0:            # 2 ramifies in Q(sqrt 2): no Frobenius; only d even survives
        return 2 ** (d * (k - 1) // 2) if d % 2 == 0 else 0
    return jacobi_symbol(2, k) ** d * 2 ** (d * (k - 1) // 2)


n = [F(0)] * (M + 1)
for m in range(1, M + 1):
    n[m] = F(K[m] - sum(n[d] * d**3 * w(d, m // d) for d in range(1, m) if m % d == 0), m**3)
bad = [d for d in range(1, M + 1) if n[d].denominator != 1]
print(f"non-integral n_d: {len(bad)} of {M}; first {bad[:10]}")
print("denominators:", [(d, n[d].denominator) for d in bad[:10]])
if not bad:
    print("n_1..n_16 =", [int(v) for v in n[1:17]])
assert not bad and M == 110
# untwisted weights w = 1, first 80
u = [F(0)] * (M + 1)
for m in range(1, M + 1):
    u[m] = F(K[m] - sum(u[d] * d**3 for d in range(1, m) if m % d == 0), m**3)
nonint = sum(1 for d in range(1, 81) if u[d].denominator != 1)
print(f"untwisted: {nonint} of the first 80 not integral")
assert nonint == 76
