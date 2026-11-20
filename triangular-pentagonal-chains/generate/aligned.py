"""Parity-aligned chains: a chain on [1..m] with each v at a position of the same parity as v
(so every adjacent sum is an odd triangular number), with prescribed endpoints."""
from __future__ import annotations
import random
from math import isqrt


def is_tri(m: int) -> bool:
    r = isqrt(8 * m + 1)
    return r * r == 8 * m + 1


def odd_tri(m: int) -> bool:
    return m % 2 == 1 and is_tri(m)


def agraph(m: int) -> dict[int, list[int]]:
    return {v: [w for w in range(1, m + 1) if w != v and odd_tri(v + w)] for v in range(1, m + 1)}


def aligned_path(m: int, a: int, b: int, tries: int = 60, steps: int = 400_000, seed: int = 1) -> list[int] | None:
    """Posa rotations with the start fixed at a; accept when the path covers [1..m] and ends at b.
    Odd/even alignment is automatic: the graph is bipartite odd-even and a is odd, so position i has parity of i."""
    if a % 2 == 0 or b % 2 != m % 2 or a == b:
        return None
    G = agraph(m)
    adj = {v: set(G[v]) for v in G}
    if any(not adj[v] for v in adj):
        return None
    rng = random.Random(seed)
    for _ in range(tries):
        path = [a]; pos = {a: 0}
        for _ in range(steps):
            v = path[-1]
            if len(path) == m:
                if v == b:
                    return path
            free = [w for w in adj[v] if w not in pos and (w != b or len(path) == m - 1)]
            if free:
                w = rng.choice(free); pos[w] = len(path); path.append(w); continue
            nb = [w for w in adj[v] if w in pos and 0 < pos[w] < len(path) - 2]
            if not nb:
                break
            w = rng.choice(nb); i = pos[w]
            path[i + 1:] = reversed(path[i + 1:])
            for j in range(i + 1, len(path)):
                pos[path[j]] = j
    return None


def check(path: list[int], m: int, a: int, b: int) -> bool:
    return (sorted(path) == list(range(1, m + 1)) and path[0] == a and path[-1] == b
            and all(odd_tri(x + y) for x, y in zip(path, path[1:]))
            and all((i + 1) % 2 == v % 2 for i, v in enumerate(path)))


if __name__ == "__main__":
    import sys
    lo, hi = int(sys.argv[1]), int(sys.argv[2])
    # any endpoints: which m have an aligned chain at all?
    for m in range(lo, hi + 1):
        ok = []
        for a in range(1, min(m, 30) + 1, 2):
            for b in range(2 - m % 2, min(m, 30) + 1, 2):
                p = aligned_path(m, a, b, tries=3, steps=20000)
                if p and check(p, m, a, b):
                    ok.append((a, b))
        print(m, len(ok), ok[:12])
