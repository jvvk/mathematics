"""The search behind "How the example was found" (Section 5 of paper/mex.tex).

Runs the mex rule for every starting word of zeros and ones of length 1 to 8, for 3000 terms each,
and checks the three claims quoted in the paper:
  * no word of length at most 7 produces a value above 30;
  * among the 256 words of length 8, exactly one produces a value above 100;
  * that word is 1,1,1,0,1,0,1,1, and its first 3000 terms reach 797.

Run: python3 search.py   (NumPy; single core, under a minute)
"""

from __future__ import annotations

import itertools

import numpy as np

N_TERMS = 3000


def max_value(word: tuple[int, ...], n_terms: int = N_TERMS) -> int:
    """Largest of the first n_terms terms of the mex sequence started from word."""
    a = np.zeros(n_terms, dtype=np.int64)
    a[: len(word)] = word
    for n in range(len(word) - 1, n_terms - 1):
        sums = a[: n + 1] + a[n::-1]
        seen = np.zeros(2 * int(sums.max()) + 2, dtype=bool)
        seen[sums] = True
        a[n + 1] = int(np.argmin(seen))
    return int(a.max())


def main() -> None:
    best: dict[int, list[tuple[tuple[int, ...], int]]] = {}
    for length in range(1, 9):
        best[length] = [(w, max_value(w)) for w in itertools.product((0, 1), repeat=length)]
        top = max(m for _, m in best[length])
        print(f"length {length}: {len(best[length])} words, largest value {top}")
    short = max(m for length in range(1, 8) for _, m in best[length])
    big = [(w, m) for w, m in best[8] if m > 100]
    assert short <= 30, short
    assert len(big) == 1, big
    assert big[0] == ((1, 1, 1, 0, 1, 0, 1, 1), 797), big
    print("PASS no word of length <= 7 exceeds 30; one word of length 8 exceeds 100:", big[0])


if __name__ == "__main__":
    main()
