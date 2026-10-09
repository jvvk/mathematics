"""Brute-force check of primesig_pairs.two_prime: for every n <= X, factor n with a smallest-prime
sieve and compare the numbers of signature {2,2} and {3,2} with the lists the search builds.
Usage: python3 test_primesig_pairs.py [X]   (default 10**7)"""
from __future__ import annotations

import sys
from pathlib import Path

import numpy as np

sys.path.insert(0, str(Path(__file__).parent))
from primesig_pairs import candidate_primes, two_prime  # noqa: E402


def signatures(x: int) -> dict[tuple[int, ...], set[int]]:
    spf = np.zeros(x + 1, dtype=np.int64)
    for i in range(2, x + 1):
        if spf[i] == 0:
            spf[i::i][spf[i::i] == 0] = i
    out: dict[tuple[int, ...], set[int]] = {(2, 2): set(), (3, 2): set()}
    for n in range(2, x + 1):
        m, exps = n, []
        while m > 1:
            p, e = spf[m], 0
            while m % p == 0:
                m //= p
                e += 1
            exps.append(e)
        sig = tuple(sorted(exps, reverse=True))
        if sig in out:
            out[sig].add(n)
    return out


def main(x: int) -> None:
    truth = signatures(x)
    ps = candidate_primes(x)
    for (a, b), want in truth.items():
        got = set(two_prime(a, b, x, ps).tolist())
        missing, extra = sorted(want - got), sorted(got - want)
        assert not missing and not extra, f"{a}{b}: missing {missing[:5]} extra {extra[:5]}"
        print(f"signature {a}{b}: {len(want)} numbers up to {x}, lists agree")


if __name__ == "__main__":
    main(int(sys.argv[1]) if len(sys.argv) > 1 else 10**7)
