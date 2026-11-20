"""Independent nonexistence check (subset DP; small_cases.py uses DFS): no pentagonal chain for n = 2, 3;
no pentagonal necklace for 3 <= n <= 8. Controls: chain at 4, necklace at 9 and 10."""
PENT = {k * (3 * k - 1) // 2 for k in range(-60, 61)}


def paths(n, start):
    adj = [[i != j and (i + 1) + (j + 1) in PENT for j in range(n)] for i in range(n)]
    reach = [0] * (1 << n)
    for v in range(n):
        if start is None or v == start:
            reach[1 << v] |= 1 << v
    for mask in range(1, 1 << n):
        e = reach[mask]
        if e:
            for v in range(n):
                if e >> v & 1:
                    for w in range(n):
                        if not mask >> w & 1 and adj[v][w]:
                            reach[mask | 1 << w] |= 1 << w
    return reach[(1 << n) - 1], adj


def has_chain(n): return paths(n, None)[0] != 0
def has_necklace(n):
    e, adj = paths(n, 0)
    return any(e >> v & 1 and adj[v][0] for v in range(1, n))


assert not any(has_chain(n) for n in (2, 3))
assert not any(has_necklace(n) for n in range(3, 9))
assert has_chain(4) and has_necklace(9) and has_necklace(10)
print("exclusions OK: no chain for 2, 3; no necklace for 3..8 (controls 4, 9, 10 found)")
