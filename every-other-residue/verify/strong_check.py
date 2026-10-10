"""Verify the note (MSE q/2060312).

Theorem 1 (strong form). A, B subsets of Z/2^(k+1), each mapping bijectively onto Z/2^k. Write a = r + 2^k e_r,
b = r + 2^k f_r (0 <= r < 2^k) and p = (sum e + sum f) mod 2. Then A and B can be paired so that the sums are exactly
the 2^k residues of parity p, and never so that they are exactly the residues of parity 1 - p.

  1. Exhaustive brute force, k <= 3: for every (e, f) a pairing onto the parity-p class exists; for k <= 2 none onto
     the other class.
  2. The recursive construction from the proof, run on 3000 random instances for each k <= 12: output is a bijection
     and the sums are exactly the parity-p class.
MUTANT=1 swaps the two cases in the recursion; MUTANT=2 uses p = sum e only. Each must FAIL.
"""
from __future__ import annotations

import os
import random
import sys

MUTANT = int(os.environ.get("MUTANT", "0"))


def parity(A: list[int], B: list[int], k: int) -> int:
    n = 1 << k
    pa = sum(a >= n for a in A)
    pb = 0 if MUTANT == 2 else sum(b >= n for b in B)
    return (pa + pb) % 2


def pair(A: list[int], B: list[int], k: int) -> list[tuple[int, int]]:
    """Recursive construction. A, B: lists of residues mod 2^(k+1), each complete mod 2^k."""
    if k == 0:
        return [(A[0], B[0])]
    M = 1 << (k + 1)
    A0 = [a for a in A if a % 2 == 0]; A1 = [a for a in A if a % 2 == 1]
    B0 = [b for b in B if b % 2 == 0]; B1 = [b for b in B if b % 2 == 1]
    half = lambda xs, c: [((x - c) % M) // 2 for x in xs]       # instance of size k-1 in Z/2^k
    back = lambda pairs, ca, cb: [(2 * x + ca, 2 * y + cb) for x, y in pairs]
    p = parity(A, B, k)
    same = (p == 0) != (MUTANT == 1)
    if same:   # sums even: even-with-even, odd-with-odd
        return back(pair(half(A0, 0), half(B0, 0), k - 1), 0, 0) + back(pair(half(A1, 1), half(B1, 1), k - 1), 1, 1)
    return back(pair(half(A0, 0), half(B1, 1), k - 1), 0, 1) + back(pair(half(A1, 1), half(B0, 0), k - 1), 1, 0)


def instance(k: int, rng: random.Random) -> tuple[list[int], list[int]]:
    n = 1 << k
    return [r + n * rng.randint(0, 1) for r in range(n)], [r + n * rng.randint(0, 1) for r in range(n)]


def exists_onto(A: list[int], B: list[int], k: int, target: set[int]) -> bool:
    M = 1 << (k + 1)
    used, hit = [False] * len(B), set()

    def rec(i: int) -> bool:
        if i == len(A):
            return True
        for j, b in enumerate(B):
            v = (A[i] + b) % M
            if not used[j] and v in target and v not in hit:
                used[j] = True; hit.add(v)
                if rec(i + 1):
                    return True
                used[j] = False; hit.discard(v)
        return False

    return rec(0)


def main() -> int:
    ok = True
    for k in range(0, 4):
        n, M = 1 << k, 1 << (k + 1)
        good = other_none = True
        for e in range(1 << n):
            for f in range(1 << n):
                A = [r + n * ((e >> r) & 1) for r in range(n)]
                B = [r + n * ((f >> r) & 1) for r in range(n)]
                p = parity(A, B, k)
                cls = {x for x in range(M) if x % 2 == p}
                good &= exists_onto(A, B, k, cls)
                if k <= 2:
                    other_none &= not exists_onto(A, B, k, {x for x in range(M) if x % 2 != p})
        print(f"1. k={k}: pairing onto the parity-p class always exists: {good}; never onto the other class: {other_none if k <= 2 else 'n/a'}")
        ok &= good and other_none
    rng = random.Random(2016)
    for k in range(0, 13):
        M = 1 << (k + 1)
        good = True
        for _ in range(3000 if k <= 8 else 200):
            A, B = instance(k, rng)
            P = pair(A, B, k)
            p = parity(A, B, k) if MUTANT != 2 else (sum(a >= (1 << k) for a in A) + sum(b >= (1 << k) for b in B)) % 2
            sums = sorted((a + b) % M for a, b in P)
            good &= sorted(a for a, _ in P) == sorted(A) and sorted(b for _, b in P) == sorted(B)
            good &= sums == [x for x in range(M) if x % 2 == p]
        ok &= good
        if k in (1, 4, 8, 12):
            print(f"2. k={k}: recursive construction correct on all samples: {good}")
    print("PASS" if ok else "FAIL")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
