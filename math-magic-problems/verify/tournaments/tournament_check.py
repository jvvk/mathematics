"""Independent check of tournament.py: separate code, no powers-of-two shortcut, no numpy.
Walks the adaptive game tree (memoised on the multiset of results so far) carrying, for every order of
ability, the exact probability (Fraction) of those results, and at the end guesses the most likely order
(rank) or winner.
Also replays the optimal policy on random orders by simulation.
Usage: python3 tournament_check.py rank|winner K N [SIMS]
"""

from __future__ import annotations

import random
import sys
from fractions import Fraction
from itertools import permutations

P = Fraction(2, 3)
MEMO: dict = {}  # results so far as a multiset -> (value, best next game); P(results | order) ignores their order


def best(
    mode: str, k: int, orders: list, probs: tuple, g: int, policy: dict, key: tuple
) -> Fraction:
    """Max over adaptive strategies of sum over orders of P(order) * P(results) * [guess correct]."""
    memo_key = (tuple(sorted(key)), g)
    if memo_key in MEMO:
        policy[tuple(sorted(key))] = MEMO[memo_key][1]
        return MEMO[memo_key][0]
    if g == 0:
        if mode == "rank":
            return max(probs)
        return max(sum(p for s, p in zip(orders, probs) if s[0] == i) for i in range(k))
    top, arg = Fraction(-1), None
    for i in range(k):
        for j in range(i + 1, k):
            tot = Fraction(0)
            for w, l in ((i, j), (j, i)):
                nxt = tuple(
                    p * (P if s.index(w) < s.index(l) else 1 - P)
                    for s, p in zip(orders, probs)
                )
                tot += best(mode, k, orders, nxt, g - 1, policy, key + ((w, l),))
            if tot > top:
                top, arg = tot, (i, j)
    policy[tuple(sorted(key))] = arg
    MEMO[memo_key] = (top, arg)
    return top


def simulate(
    mode: str, k: int, n: int, orders: list, policy: dict, sims: int, rng: random.Random
) -> float:
    hits = 0
    for _ in range(sims):
        s = rng.choice(orders)
        key: tuple = ()
        probs = [Fraction(1)] * len(orders)
        for _g in range(n):
            i, j = policy[tuple(sorted(key))]
            better = i if s.index(i) < s.index(j) else j
            worse = j if better == i else i
            w, l = (better, worse) if rng.random() < 2 / 3 else (worse, better)
            key += ((w, l),)
            probs = [
                p * (P if t.index(w) < t.index(l) else 1 - P)
                for t, p in zip(orders, probs)
            ]
        if mode == "rank":
            guess = orders[max(range(len(orders)), key=probs.__getitem__)]
            hits += guess == s
        else:
            win = max(
                range(k),
                key=lambda i: sum(p for t, p in zip(orders, probs) if t[0] == i),
            )
            hits += win == s[0]
    return hits / sims


if __name__ == "__main__":
    mode, k, n = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])
    sims = int(sys.argv[4]) if len(sys.argv) > 4 else 0
    orders = list(permutations(range(k)))
    policy: dict = {}
    v = best(
        mode, k, orders, tuple([Fraction(1, len(orders))] * len(orders)), n, policy, ()
    )
    print(f"{mode} K={k} N={n}: exact {v} = {float(v):.5f}")
    if sims:
        print(
            f"simulated {sims} tournaments: {simulate(mode, k, n, orders, policy, sims, random.Random(1)):.5f}"
        )
