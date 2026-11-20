"""Small cases. Certificates: chains for 9 <= n <= 53 and n = 2; necklaces for 12 <= n <= 53, n != 14.
Exhaustive nonexistence: chains for 3 <= n <= 8; necklaces for 3 <= n <= 11 and n = 14."""
from __future__ import annotations
import json, sys
from math import isqrt
sys.setrecursionlimit(5000)


def tri(s: int) -> bool:
    r = isqrt(8 * s + 1); return r * r == 8 * s + 1


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
    for n in [2] + list(range(9, 54)):
        cert["chains"][n] = find(n, False, False)
        assert cert["chains"][n], n
    for n in [k for k in range(12, 54) if k != 14]:
        cert["necklaces"][n] = find(n, True, False)
        assert cert["necklaces"][n], n
    none_chain = [n for n in range(3, 9) if find(n, False, True) is None]
    none_neck = [n for n in list(range(3, 12)) + [14] if find(n, True, True) is None]
    assert none_chain == list(range(3, 9)), none_chain
    assert none_neck == list(range(3, 12)) + [14], none_neck
    json.dump(cert, open("small_certificates.json", "w"))
    print("certificates written; no chain for", none_chain, "; no necklace for", none_neck)
