"""Mutation tests for check.py: each deliberate error must change an answer."""
import json, check
pos = json.load(open("positions.json"))
b5 = {(x, y): c for x, y, c in pos["5"]}
bad = dict(b5); bad[(0, 0)] = 2                     # recolour one bishop
print("recoloured bishop rejected:", not check.attacks_ok(bad, 5))
print("B(2,5), B(2,6) =", check.B(5, 2), check.B(6, 2), "(page: 12, 18)")
orig = check.vectors
def loose(N, parity, C=3):                          # mutant: one matching diagonal suffices
    from itertools import product
    cells = [(x, y) for x in range(N) for y in range(N) if (x + y) % 2 == parity]
    s = sorted({x + y for x, y in cells}); d = sorted({x - y for x, y in cells})
    cl = [(s.index(x + y), len(s) + d.index(x - y)) for x, y in cells]
    out = set()
    for a in product(range(C + 1), repeat=len(s) + len(d)):
        v = [0] * (C + 1)
        for p, q in cl:
            v[a[p] if a[p] else a[q]] += 1
        out.add(tuple(v[1:]))
    return out
check.vectors = loose
print("loose-diagonal mutant B(3,5) =", check.B(5), "(must exceed 5)")
check.vectors = orig
