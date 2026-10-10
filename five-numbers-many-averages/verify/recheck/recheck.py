"""Independent recheck of "Five numbers, many averages", sharing no code with check.py or family_verify.py.

Integers only: the integer tuple (5N, 0, 4N, 3N+5e, 3N+5e), N = 2^(k+1), e = (-1)^k, is multiplied by 2^D so that
every average within D moves stays an integer. An iterative-deepening search over labelled tuples finds the
least number of moves for k = 1..5 and returns a witness, which is replayed. Also: no nonempty proper subset
has the mean for k = 2..30 (bitmasks), and one does for k = 1.

    timeout 600 nice -n 15 ~/.venvs/main/bin/python recheck.py
"""
from __future__ import annotations

import sys
from functools import lru_cache


def tuple_k(k: int, third: int = 4) -> list[int]:
    N, e = 2 ** (k + 1), (-1) ** k
    return [5 * N, 0, third * N, 3 * N + 5 * e, 3 * N + 5 * e]


def solve(x: list[int], depth: int, fix: int = 2) -> list[tuple[int, int]] | None:
    """Labelled iterative deepening: a sequence of at most `depth` moves making all entries equal, or None."""
    D = depth
    start = tuple(v * 2 ** D for v in x)
    total = sum(start)
    if total % 5:
        return None
    mean = total // 5

    @lru_cache(maxsize=None)
    def dfs(state: tuple[int, ...], left: int) -> tuple | None:
        if all(v == mean for v in state):
            return ()
        if left == 0:
            return None
        off = sum(v != mean for v in state)
        if off > fix * left:  # each move fixes at most two entries
            return None
        for i in range(5):
            for j in range(i + 1, 5):
                if state[i] == state[j]:
                    continue
                s = list(state)
                s[i] = s[j] = (state[i] + state[j]) // 2
                rest = dfs(tuple(s), left - 1)
                if rest is not None:
                    return ((i, j),) + rest
        return None

    for d in range(depth + 1):
        w = dfs(start, d)
        if w is not None:
            return list(w)
    return None


def replay(x: list[int], w: list[tuple[int, int]]) -> bool:
    from fractions import Fraction
    y = [Fraction(v) for v in x]
    for i, j in w:
        y[i] = y[j] = (y[i] + y[j]) / 2
    return len(set(y)) == 1


def balanced_subsets(x: list[int]) -> list[int]:
    tot = sum(x)
    return [m for m in range(1, 31) if 5 * sum(x[i] for i in range(5) if m >> i & 1) == bin(m).count("1") * tot]


def run(fix: int = 2, claim=lambda k: k + 3, third: int = 4) -> int:
    n = 0
    for k in range(1, 6):
        x = tuple_k(k, third)
        w = solve(x, k + 4, fix)
        assert w is not None and len(w) == claim(k), (k, w)
        assert replay(x, w), (k, w)
        n += 2
        print(f"k={k}: {x} least moves {len(w)}: {w}", flush=True)
    for k in range(1, 31):
        b = balanced_subsets(tuple_k(k, third))
        assert (not b) == (k >= 2), (k, b)
        n += 1
    assert tuple_k(2) == [40, 0, 32, 29, 29]
    return n + 1


if __name__ == "__main__":
    print(f"positive: {run()} checks passed\n", flush=True)
    mutants = {
        "pruning assumes a move fixes only one entry": dict(fix=1),
        "optimum claimed k + 2": dict(claim=lambda k: k + 2),
        "third entry 5N instead of 4N": dict(third=5),
    }
    for name, kw in mutants.items():
        try:
            run(**kw)
        except AssertionError as e:
            print(f"rejected mutant: {name} ({e})\n", flush=True)
        else:
            sys.exit(f"UNDETECTED MUTANT: {name}")
    print(f"all {len(mutants)} mutants rejected")
