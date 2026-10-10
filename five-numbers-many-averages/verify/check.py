"""Assert every number stated in "Five numbers, many averages", then reject deliberate mutants.

Exact arithmetic (fractions). Checks: the k = 2 example of Figure 1 (states, mean 26, the count column
0,0,2,1,3,5); the triple of Figure 2; the strategy of k + 3 moves for k = 1..60; the least number of moves
k + 3 for k = 1..4 by complete breadth-first search over all move sequences; the integer form; no balanced
proper subset for k = 2..40 and one for k = 1.

    timeout 600 nice -n 15 ~/.venvs/main/bin/python check.py
"""
from __future__ import annotations

import itertools
import sys
from fractions import Fraction as Fr

PAIRS = list(itertools.combinations(range(5), 2))


def t(k: int) -> Fr:
    return Fr(-1, 2) ** k


def B(k: int, c3: Fr = Fr(5, 2)) -> tuple[Fr, ...]:
    return (Fr(2), Fr(-3), Fr(1), c3 * t(k), Fr(5, 2) * t(k))


def move(x: tuple, p: tuple[int, int]) -> tuple:
    y = list(x)
    y[p[0]] = y[p[1]] = (x[p[0]] + x[p[1]]) / 2
    return tuple(y)


def least_moves(x: tuple, cap: int, pairs=PAIRS) -> int | None:
    """Complete breadth-first search over multisets of entries; None if more than cap moves are needed."""
    mu = sum(x) / len(x)
    goal = tuple(sorted([mu] * len(x)))
    frontier, seen = {tuple(sorted(x))}, {tuple(sorted(x))}
    for d in range(cap + 1):
        if goal in frontier:
            return d
        nxt = set()
        for s in frontier:
            for p in pairs:
                y = tuple(sorted(move(s, p)))
                if y not in seen:
                    seen.add(y)
                    nxt.add(y)
        frontier = nxt
    return None


def strategy(k: int) -> list[tuple[int, int]]:
    sing = lambda m: 1 if m % 2 == 0 else 2
    return [(0, 1)] + [(sing(m), 0) for m in range(1, k + 1)] + [(0, 3), (sing(k), 4)]


def check(claim_opt=lambda k: k + 3, c3: Fr = Fr(5, 2), pairs=PAIRS, strat=strategy, kmax_search: int = 6) -> int:
    n = 0
    # Figure 1
    rows = [(40, 0, 32, 29, 29), (20, 20, 32, 29, 29), (26, 20, 26, 29, 29), (26, 23, 23, 29, 29),
            (26, 26, 23, 26, 29), (26, 26, 26, 26, 26)]
    used = [(0, 1), (0, 2), (1, 2), (1, 3), (2, 4)]
    for a, b, p in zip(rows, rows[1:], used):
        assert move(tuple(map(Fr, a)), p) == tuple(map(Fr, b)), (a, p)
    assert [r.count(26) for r in rows] == [0, 0, 2, 1, 3, 5]
    assert sum(rows[0]) == 5 * 26
    n += 7
    # integer form = N * B_k + 3N, and the k = 2 example
    for k in range(1, 61):
        N, e = 2 ** (k + 1), (-1) ** k
        assert tuple(N * v + 3 * N for v in B(k, c3)) == (5 * N, 0, 4 * N, 3 * N + 5 * e, 3 * N + 5 * e), k
        assert sum(B(k, c3)) == 5 * t(k)
        n += 2
    assert tuple(8 * v + 24 for v in B(2, c3)) == rows[0]
    # Figure 2: the triple after move m is (s, s, -2s) with s = (-1/2)^m, and the strategy works in k + 3 moves
    for k in range(1, 61):
        x = B(k, c3)
        for m, p in enumerate(strat(k)):
            x = move(x, p)
            if m + 1 <= k:
                s = Fr(-1, 2) ** (m + 1)
                assert sorted(x[:3]) == sorted([s, s, -2 * s]), (k, m)
        assert len(strat(k)) == claim_opt(k) and all(v == t(k) for v in x), k
        n += 1
    # least number of moves by complete search
    for k in range(1, kmax_search + 1):
        assert least_moves(B(k, c3), k + 4, pairs) == claim_opt(k), k
        assert least_moves(tuple(map(Fr, rows[0])), 6, pairs) == 5
        n += 2
    # balanced proper subsets
    for k in range(1, 41):
        x = B(k, c3)
        bal = [S for r in range(1, 5) for S in itertools.combinations(range(5), r)
               if sum(x[i] for i in S) == len(S) * t(k)]
        assert (bal == []) == (k >= 2), (k, bal)
        n += 1
    return n


if __name__ == "__main__":
    print(f"positive: {check()} assertions passed", flush=True)
    mutants = {
        "optimum claimed k + 2": dict(claim_opt=lambda k: k + 2),
        "tuple with 3t/2": dict(c3=Fr(3, 2)),
        "search never averages the smallest entry": dict(pairs=[q for q in PAIRS if 0 not in q]),
        "strategy without its last move": dict(strat=lambda k: strategy(k)[:-1]),
    }
    for name, kw in mutants.items():
        try:
            check(**kw, kmax_search=3)
        except AssertionError as e:
            print(f"rejected mutant: {name} ({e})", flush=True)
        else:
            sys.exit(f"UNDETECTED MUTANT: {name}")
    print(f"all {len(mutants)} mutants rejected")
