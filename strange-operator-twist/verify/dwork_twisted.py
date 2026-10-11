"""Test the twisted Dwork congruences predicted by Beukers-Vlasenko Thm 1.7 with lift q^σ = c_p q^p:
(C_p): K_n ≡ c_p^(n/p) K_(n/p)  (mod p^(3 v_p(n)))  for all n ≤ N, p odd,  c_p = (2/p) 2^((p-1)/2).
Control: the untwisted c_p = 1 must fail."""
import json
from sympy import legendre_symbol, factorint

K = json.load(open("K110.json"))
N = len(K) - 1
odd_primes = [p for p in range(3, N + 1) if all(p % r for r in range(2, int(p**.5) + 1))]


def test(cfun):
    fails, checked = [], 0
    for p in odd_primes:
        c = cfun(p)
        for n in range(p, N + 1, p):
            v = factorint(n).get(p, 0)
            m = p ** (3 * v)
            checked += 1
            if (K[n] - pow(c, n // p) * K[n // p]) % m:
                fails.append((p, n))
    return checked, fails


for name, cf in [("twisted c_p = (2/p) 2^((p-1)/2)", lambda p: legendre_symbol(2, p) * 2 ** ((p - 1) // 2)),
                 ("untwisted c_p = 1", lambda p: 1),
                 ("wrong sign c_p = 2^((p-1)/2)", lambda p: 2 ** ((p - 1) // 2)),
                 ("wrong base c_p = (3/p) 3^((p-1)/2)", lambda p: legendre_symbol(3, p) * 3 ** ((p - 1) // 2) if p != 3 else 1)]:
    checked, fails = test(cf)
    print(f"{name:38s}: {checked - len(fails)}/{checked} congruences hold; first failures {fails[:5]}")
