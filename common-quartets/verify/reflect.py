"""Reflection families: leaves c-h..c+h (h = 2^(k-1)), order pi_D puts label c-d at position c+d (and back) for d in D.
Search k subsets D_1 = {} , D_2, ..., D_k of {1..h} with no common caterpillar quartet."""
import sys
from itertools import combinations

sys.path.insert(0, __file__.rsplit("/", 1)[0])
from caterpillar import cat_split  # noqa: E402


def order(h: int, D: frozenset) -> list[int]:
    # positions -h..h; label at position p
    return [(-p if abs(p) in D else p) for p in range(-h, h + 1)]


def search(k: int):
    h = 2 ** (k - 1)
    X = list(range(-h, h + 1))
    quads = list(combinations(X, 4))
    subsets = [frozenset(s) for r in range(h + 1) for s in combinations(range(1, h + 1), r)]
    split = {D: [cat_split(order(h, D), Q) for Q in quads] for D in subsets}
    base = split[frozenset()]
    alive0 = [i for i in range(len(quads))]  # quartets still common to all chosen orders

    def rec(chosen, alive, start):
        if not alive:
            return chosen
        if len(chosen) == k:
            return None
        for j in range(start, len(subsets)):
            D = subsets[j]
            s = split[D]
            na = [i for i in alive if s[i] == base[i]]
            r = rec(chosen + [D], na, j + 1)
            if r:
                return r
        return None

    return rec([frozenset()], alive0, 1)


if __name__ == "__main__":
    for k in (2, 3, 4):
        r = search(k)
        print(f"k={k}, n={2**k+1}:", [sorted(D) for D in r] if r else "none of reflection form")
