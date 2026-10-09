"""Optimal adaptive tournaments (Math Magic, February 2020; unsolved no. 33).

K players in a hidden random order of ability; the better player wins each game with probability 2/3.
N games are played one after another, each chosen knowing all earlier results; then we guess.
A history H is a multiset of results "i beat j". For an order s, P(H | s) = 2^agree(s, H) / 3^|H|, where
agree counts results consistent with s. With a uniform prior over the K! orders:
  rank  : P(correct order)  = sum over final H of max_s 2^agree(s,H)            / (3^N K!)
  winner: P(correct winner) = sum over final H of max_i sum_{s: s(1)=i} 2^agree / (3^N K!)
Playing all N games never hurts (a result can be ignored), so the optimum is an exact integer recursion:
W(H, g) = max over pairs {i,j} of W(H + "i beat j", g-1) + W(H + "j beat i", g-1).
Usage: python3 tournament.py rank|winner K N
"""

from __future__ import annotations

import sys
from fractions import Fraction
from functools import cache
from itertools import permutations

import numpy as np


def solve(mode: str, k: int, n: int, want_tree: bool = False):
    """Optimal probability as a Fraction; with want_tree, also one optimal strategy as a nested dict
    {"game": [i, j], "i": subtree if i wins, "j": subtree if j wins} with leaves {"guess": order or winner}."""
    ordered = [(i, j) for i in range(k) for j in range(k) if i != j]
    idx = {r: t for t, r in enumerate(ordered)}
    perms = list(permutations(range(k)))
    # agree matrix: A[s, t] = 1 if order s puts the winner of result t above its loser
    A = np.zeros((len(perms), len(ordered)), dtype=np.int64)
    for a, s in enumerate(perms):
        pos = {p: r for r, p in enumerate(s)}
        for (i, j), t in idx.items():
            A[a, t] = pos[i] < pos[j]
    top = np.array([s[0] for s in perms])
    pairs = [(i, j) for i in range(k) for j in range(i + 1, k)]

    def leaf(h: tuple[int, ...]) -> int:
        w = 2 ** (
            A @ np.array(h, dtype=np.int64)
        )  # 2^agree for every order (fits: agree <= n)
        if mode == "rank":
            return int(w.max())
        return int(max(w[top == i].sum() for i in range(k)))

    @cache
    def W(h: tuple[int, ...], g: int) -> int:
        if g == 0:
            return leaf(h)
        best = 0
        for i, j in pairs:
            a, b = list(h), list(h)
            a[idx[(i, j)]] += 1
            b[idx[(j, i)]] += 1
            best = max(best, W(tuple(a), g - 1) + W(tuple(b), g - 1))
        return best

    def tree(h: tuple[int, ...], g: int) -> dict:
        if g == 0:
            w = 2 ** (A @ np.array(h, dtype=np.int64))
            if mode == "rank":
                return {"guess": list(perms[int(w.argmax())])}
            return {"guess": int(max(range(k), key=lambda i: w[top == i].sum()))}
        for i, j in pairs:  # first optimal game in a fixed order
            a, b = list(h), list(h)
            a[idx[(i, j)]] += 1
            b[idx[(j, i)]] += 1
            if W(tuple(a), g - 1) + W(tuple(b), g - 1) == W(h, g):
                return {"game": [i, j], "i": tree(tuple(a), g - 1), "j": tree(tuple(b), g - 1)}
        raise AssertionError("no optimal game")

    root = tuple([0] * len(ordered))
    value = Fraction(W(root, n), 3**n * len(perms))
    return (value, tree(root, n)) if want_tree else value


if __name__ == "__main__":
    mode, k, n = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])
    f = solve(mode, k, n)
    print(f"{mode} K={k} N={n}: {f} = {float(f):.5f}")
