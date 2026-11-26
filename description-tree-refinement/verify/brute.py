"""Brute force: (2,2) description trees with s edges, distribution of nu. Independent of any GF."""
import sys as _sys
if not __debug__:
    _sys.exit("refusing to run under python -O: the checks are assertions")
from functools import lru_cache
from collections import Counter
import sys

@lru_cache(None)
def planted(e):
    """Subtrees with e edges (counting edges inside), as Counter{(label, nu): count}; vertex is non-root."""
    out = Counter()
    if e == 0:
        out[(2, 1)] = 1
        return out
    for (S, nu), c in forest(e).items():  # children forest with e edges total (each child edge counted)
        for lab in range(2, 2 + S + 1):
            out[(lab, nu + (lab == 2 + S))] += c
    return out

@lru_cache(None)
def forest(e):
    """Nonempty sequences of planted subtrees, total edges e (each child contributes its edges + 1)."""
    out = Counter()
    for e1 in range(0, e):
        for (l1, n1), c1 in planted(e1).items():
            rest = e - e1 - 1
            if rest == 0:
                out[(l1, n1)] += c1
            else:
                for (S, n2), c2 in forest(rest).items():
                    out[(l1 + S, n1 + n2)] += c1 * c2
    return out

def row(s):
    d = Counter()
    for (S, nu), c in forest(s).items():
        d[nu + 1] += c  # root is maximal
    return [d[n + 1] for n in range(1, s + 1)]

# Unsigned rows s = 1..8 of OEIS A336110 (data section, 2026-11-26).
A336110 = [[1], [2, 2], [5, 14, 5], [14, 74, 74, 14], [42, 352, 668, 352, 42], [132, 1588, 4808, 4808, 1588, 132],
           [429, 6946, 30371, 48540, 30371, 6946, 429],
           [1430, 29786, 176270, 407810, 407810, 176270, 29786, 1430]]

if __name__ == "__main__":
    if "--check" in sys.argv:  # the brute-force rows agree with the A336110 data for s <= 8
        for s, r in enumerate(A336110, 1):
            assert row(s) == r, (s, row(s), r)
        print("brute-force rows = A336110 data for s <= 8")
        sys.exit(0)
    N = int(sys.argv[1]) if len(sys.argv) > 1 else 9
    for s in range(1, N + 1):
        print(s, row(s), sum(row(s)))
