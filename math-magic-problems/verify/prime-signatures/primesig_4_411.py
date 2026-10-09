"""Smallest n = p^4 with n+1 of prime signature {4,1,1} (a "?" cell of the February 2018 table).

For odd p, p^4 + 1 = 2 (mod 16), so n+1 = 2 q^4 r with q, r odd distinct primes; q^4 | p^4 + 1 forces
q = 1 (mod 8). For each such q <= P, lift the four roots of x^4 = -1 (mod q) to mod q^4 (Hensel) and test
every prime p <= P in those classes. p = 2 gives 17, not of this form.
Usage: python3 primesig_4_411.py P
"""

from __future__ import annotations

import sys

from sympy import isprime, nthroot_mod, primerange


def roots_mod_q4(q: int) -> list[int]:
    m = q**4
    out = []
    for x in nthroot_mod(q - 1, 4, q, all_roots=True):
        for k in (2, 3, 4):  # lift x from mod q^(k-1) to mod q^k
            mk = q**k
            fx, dfx = (x**4 + 1) % mk, (4 * x**3) % q
            x = (x - fx * pow(dfx, -1, q)) % mk
        assert (x**4 + 1) % m == 0
        out.append(x)
    return out


def main(pmax: int) -> None:
    best = None
    for q in primerange(17, pmax + 1):
        if q % 8 != 1:
            continue
        m = q**4
        for r0 in roots_mod_q4(q):
            for p in range(r0, pmax + 1, m):
                if p > 2 and isprime(p):
                    rest = (p**4 + 1) // (2 * m)
                    if rest % q and isprime(rest) and (best is None or p < best):
                        best = p
    print(f"smallest prime p <= {pmax} with p^4+1 = 2 q^4 r: {best}")


if __name__ == "__main__":
    main(int(sys.argv[1]))
