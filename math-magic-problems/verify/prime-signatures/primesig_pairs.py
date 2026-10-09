"""Direct search for consecutive numbers with two-prime signatures (unsolved no. 28).

Lists every n = p^a q^b <= X (p != q primes) for the signature {a, b}, sorts, and looks for n, n+1 with
n of signature A and n+1 of signature B. Complements primesig.py (the Pell search for A={2,2}, B={3,2}).
Usage: python3 primesig_pairs.py LOG10_X
Checked against brute-force factorisation by test_primesig_pairs.py.
"""

from __future__ import annotations

import sys

import numpy as np


def primes_upto(m: int) -> np.ndarray:
    s = np.ones(m + 1, dtype=bool)
    s[:2] = False
    for i in range(2, int(m**0.5) + 1):
        if s[i]:
            s[i * i :: i] = False
    return np.nonzero(s)[0].astype(np.int64)


def two_prime(a: int, b: int, x: int, ps: np.ndarray) -> np.ndarray:
    """All p^a q^b <= x with p != q prime (a >= b)."""
    out = []
    for p in ps:
        pa = int(p) ** a
        if pa * 2**b > x:
            break
        lim = int((x // pa) ** (1 / b)) + 2
        qs = ps[: np.searchsorted(ps, lim, side="right")]
        qs = qs[qs != p]
        v = pa * qs**b
        out.append(v[v <= x])
    return np.unique(np.concatenate(out))


def candidate_primes(x: int) -> np.ndarray:
    """Every prime that can appear in p^2 q^2 <= x or p^3 q^2 <= x. The largest is q in 4 q^2 <= x, so the
    list must reach sqrt(x / 4); an earlier bound of sqrt(x / 8) missed n = 4 q^2 with q just below it."""
    return primes_upto(int((x / 4) ** 0.5) + 2)


def main(k: int) -> None:
    x = 10**k
    ps = candidate_primes(x)
    s22, s32 = two_prime(2, 2, x, ps), two_prime(3, 2, x, ps)
    for name, a, b in (
        ("{2,2} -> {3,2}", s22, s32),
        ("{3,2} -> {3,2}", s32, s32),
        ("{3,2} -> {2,2}", s32, s22),
    ):
        hits = a[np.isin(a + 1, b)]
        print(f"{name}: {len(a)} candidates n <= 10^{k}, hits {hits.tolist()}")


if __name__ == "__main__":
    main(int(sys.argv[1]))
