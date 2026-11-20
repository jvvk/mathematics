"""Independent check of the nonexistence claims (no code shared with small_cases.py, different algorithm):
bitmask dynamic programming over subsets. reach[mask][v] = there is a path through exactly the vertices of
`mask` ending at v. No chain on [1..n] for 3 <= n <= 8; no necklace for 3 <= n <= 11 and n = 14.
Also confirms existence at the boundary values (chain at 2 and 9, necklace at 12, 13, 15) as a control."""
TRI = {k * (k + 1) // 2 for k in range(100)}


def paths(n: int, start: int | None):
    adj = [[(i + 1) + (j + 1) in TRI and i != j for j in range(n)] for i in range(n)]
    full = (1 << n) - 1
    reach = [0] * (1 << n)  # bitmask of end vertices
    for v in range(n):
        if start is None or v == start:
            reach[1 << v] |= 1 << v
    for mask in range(1, 1 << n):
        ends = reach[mask]
        if not ends:
            continue
        for v in range(n):
            if ends >> v & 1:
                for w in range(n):
                    if not (mask >> w & 1) and adj[v][w]:
                        reach[mask | 1 << w] |= 1 << w
    return reach[full], adj


def has_chain(n: int) -> bool:
    return paths(n, None)[0] != 0


def has_necklace(n: int) -> bool:
    ends, adj = paths(n, 0)  # a necklace passes through 1, so start there
    return any(ends >> v & 1 and adj[v][0] for v in range(1, n))


assert not any(has_chain(n) for n in range(3, 9))
assert not any(has_necklace(n) for n in list(range(3, 12)) + [14])
assert has_chain(2) and has_chain(9) and all(has_necklace(n) for n in (12, 13, 15))
print("exclusions OK: no chain for 3..8; no necklace for 3..11, 14 (controls 2, 9, 12, 13, 15 found)")
