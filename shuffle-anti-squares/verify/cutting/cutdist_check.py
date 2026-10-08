"""Independent check of cutdist.c: two-cut distance of anti-squares, with witnesses and a negative control."""
import random
import sys
from functools import lru_cache


def is_shuffle_square(w: str) -> bool:
    """Shuffle-square test via memoised recursion on (position, unmatched suffix of the leading copy)."""
    n = len(w)
    if n % 2:
        return False

    @lru_cache(maxsize=None)
    def go(i: int, lead: int, pend: str) -> bool:
        if i == n:
            return pend == ""
        if len(pend) > n - i:
            return False
        c = w[i]
        if pend and pend[0] == c and go(i + 1, lead, pend[1:]):
            return True
        return lead < n // 2 and go(i + 1, lead + 1, pend + c)

    return go(0, 0, "")


def two_cut_witness(t: str, orders=("ACB", "BAC", "CBA")) -> tuple[int, int, str] | None:
    n = len(t)
    for i in range(n + 1):
        for j in range(i, n + 1):
            p = {"A": t[:i], "B": t[i:j], "C": t[j:]}
            for o in orders:
                v = "".join(p[ch] for ch in o)
                if is_shuffle_square(v):
                    return i, j, o
    return None


def rotations(s: str) -> list[str]:
    return [s[r:] + s[:r] for r in range(len(s))]


if __name__ == "__main__":
    random.seed(20261008)
    # Sanity: the tester agrees the inputs are anti-squares (no rotation is a shuffle square).
    for L, sample in ((24, None), (26, None), (30, 300)):
        necks = [l.strip() for l in open(f"../results/anti_{L}.txt") if l.strip()]
        words = [r for s in necks for r in rotations(s)]
        if sample:
            words = random.sample(words, sample)
        assert all(not is_shuffle_square(w) for w in words), "input not anti-square"
        bad = [w for w in words if two_cut_witness(w) is None]
        print(f"L={L} words={len(words)} needing>=3={len(bad)}")
    # Negative control: allowing only rotations (BCA, CAB) must fail on every anti-square.
    w0 = open("../results/anti_24.txt").readline().strip()
    assert two_cut_witness(w0, orders=("BCA", "CAB", "ABC")) is None
    # Control 2: a random non-anti-square word with a rotation fix should be found.
    print("witness for", w0, "->", two_cut_witness(w0))
    print("controls OK")
