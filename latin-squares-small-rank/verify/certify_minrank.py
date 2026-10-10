"""Exact certificate for the minimum real rank r(n) of an n x n Latin square on 1..n, n = 4..7.

Every Latin square is, up to row and column order (which do not change rank), an isotopy-class
representative (B. D. McKay's lists, data/latin_isN.txt) with its symbols given the values 1..n in some
order. For each of the (#classes) x n! matrices this computes the rank modulo the prime p = 2^31 - 1 by
batched Gaussian elimination. Since rank mod p <= rank over Q, "rank mod p >= r for all" certifies
r(n) >= r exactly; a witness of rank r (exact, sympy) gives r(n) <= r.
Usage: python3 certify_minrank.py [n ...]      (default 4 5 6 7; n = 7 is 2.8 million matrices)
Mutant: --mutant computes ranks modulo 3 instead; ranks then drop, and the run must fail (a different
minimum, or the exact witness check).
"""
import sys
from itertools import permutations
import numpy as np
import sympy as sp

P = 2 ** 31 - 1
CLAIM = {4: 3, 5: 5, 6: 4, 7: 6}
CLASSES = {4: 2, 5: 2, 6: 22, 7: 564}   # OEIS A040082


def load(n: int) -> list[np.ndarray]:
    reps = [np.array([int(c) for c in s]).reshape(n, n) for s in open(f"data/latin_is{n}.txt").read().split()]
    assert len(reps) == CLASSES[n], (n, len(reps))
    for L in reps:  # each representative is a Latin square on 0..n-1
        assert all(sorted(r) == list(range(n)) for r in L) and all(sorted(c) == list(range(n)) for c in L.T)
    return reps


def rank_mod_p(M: np.ndarray, mutant: bool = False) -> np.ndarray:
    """Ranks mod P of a batch (b, n, n) of integer matrices, by Gaussian elimination."""
    P = 3 if mutant else globals()["P"]
    M = (M % P).astype(np.int64)
    b, n, _ = M.shape
    rank = np.zeros(b, dtype=np.int64)
    row = np.zeros(b, dtype=np.int64)
    idx = np.arange(b)
    for c in range(n):
        # choose a pivot at or below the current row in column c
        sub = M[:, :, c].copy()
        mask = np.arange(n)[None, :] >= row[:, None]
        cand = (sub != 0) & mask
        has = cand.any(axis=1)
        piv = np.where(has, cand.argmax(axis=1), 0)
        h = idx[has]
        if len(h) == 0:
            continue
        r0, pr = row[h], piv[h]
        tmp = M[h, r0, :].copy()
        M[h, r0, :] = M[h, pr, :]
        M[h, pr, :] = tmp
        inv = np.array([pow(int(v), P - 2, P) for v in M[h, r0, c]], dtype=np.int64)
        M[h, r0, :] = (M[h, r0, :] * inv[:, None]) % P
        for rr in range(n):
            f = M[h, rr, c].copy()
            f[rr == r0] = 0
            M[h, rr, :] = (M[h, rr, :] - (f[:, None] * M[h, r0, :]) % P) % P
        row[h] += 1
        rank[h] += 1
    return rank


def certify(n: int, mutant: bool = False) -> int:
    reps = load(n)
    perms = np.array(list(permutations(range(1, n + 1))))
    best, wit = n + 1, None
    for L in reps:
        M = perms[:, L]                     # all n! value assignments
        r = rank_mod_p(M, mutant)
        k = int(r.argmin())
        if r[k] < best:
            best, wit = int(r[k]), M[k]
    exact = sp.Matrix(wit.tolist()).rank()
    assert exact == best, (n, exact, best)   # the witness attains the bound over Q
    return best


if __name__ == "__main__":
    mutant = "--mutant" in sys.argv
    ns = [int(a) for a in sys.argv[1:] if a != "--mutant"] or [4, 5, 6, 7]
    for n in ns:
        r = certify(n, mutant)
        status = "OK" if r == CLAIM[n] else "DIFFERS FROM CLAIM"
        print(f"n={n}: rank mod p >= {r} for all {CLASSES[n]} classes x {n}! valuations; "
              f"witness of exact rank {r}. r({n}) = {r} {status}", flush=True)
