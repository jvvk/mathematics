"""Small cases (generalized pentagonal sums k(3k-1)/2, k in Z). Certificates: chains for 4 <= n <= 59;
necklaces for 9 <= n <= 59. Exhaustive nonexistence: chains for n = 2, 3; necklaces for 3 <= n <= 8."""
from __future__ import annotations
import json, sys
from math import isqrt
sys.setrecursionlimit(5000)


def tri(s: int) -> bool:  # true iff s is a generalized pentagonal number (name kept from the triangular code)
    d = 24 * s + 1; r = isqrt(d); return r * r == d and r % 6 in (1, 5)


def nbrs(n: int) -> dict[int, list[int]]:
    return {v: [w for w in range(1, n + 1) if w != v and tri(v + w)] for v in range(1, n + 1)}


def find(n: int, cycle: bool, exhaustive: bool):
    """DFS; with exhaustive=True explores everything (returns None only if none exists)."""
    G = nbrs(n)
    starts = [1] if cycle else list(range(1, n + 1))
    for s in starts:
        path, used = [s], {s}

        def dfs():
            v = path[-1]
            if len(path) == n:
                return (not cycle) or tri(path[0] + v)
            for w in sorted(G[v], key=lambda u: len([x for x in G[u] if x not in used])):
                if w not in used:
                    used.add(w); path.append(w)
                    if dfs():
                        return True
                    used.discard(w); path.pop()
            return False

        if dfs():
            return list(path)
    return None


if __name__ == "__main__":
    cert = {"chains": {}, "necklaces": {}}
    for n in range(4, 60):
        cert["chains"][n] = find(n, False, False)
        assert cert["chains"][n], n
    for n in range(9, 60):
        cert["necklaces"][n] = find(n, True, False)
        assert cert["necklaces"][n], n
    none_chain = [n for n in range(2, 4) if find(n, False, True) is None]
    none_neck = [n for n in range(3, 9) if find(n, True, True) is None]
    assert none_chain == [2, 3], none_chain
    assert none_neck == list(range(3, 9)), none_neck
    json.dump(cert, open("small_certificates.json", "w"))
    print("certificates written; no chain for", none_chain, "; no necklace for", none_neck)
