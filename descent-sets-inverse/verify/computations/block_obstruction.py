"""Count pairs (S,T) of subsets of [n-1] killed by the block obstruction:
T contains |S|+1 consecutive integers (or S contains |T|+1). Such pairs never occur:
the values i..i+|S|+1 appear in decreasing order in w, but w has only |S|+1 ascending runs."""
import sys
from collections import Counter


def stats(n):
    c = Counter()  # (size, longest block) -> number of subsets
    for mask in range(1 << (n - 1)):
        size = bin(mask).count("1")
        best = cur = 0
        m = mask
        while m:
            if m & 1:
                cur += 1
                best = max(best, cur)
            else:
                cur = 0
            m >>= 1
        c[(size, best)] += 1
    return c


def blocked(n):
    c = stats(n)
    items = list(c.items())
    tot = 0
    for (s, bs), ns in items:
        for (t, bt), nt in items:
            if bt >= s + 1 or bs >= t + 1:
                tot += ns * nt
    return tot


if __name__ == "__main__":
    for n in range(2, int(sys.argv[1]) + 1):
        b = blocked(n)
        print(n, b, round(b / 4 ** (n - 1), 6), flush=True)
