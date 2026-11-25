"""Independent check of Theorem 2 (no SAT, no code shared with the search): G9 as defined in the note has 28 edges and
no strongly non-nested 4-matching; the graphs obtained by adding vertices joined to 1, 2, 3 keep this, for n <= 12."""
import itertools
def G9():
    A, B = [1, 2, 3], range(4, 10)
    E = set(itertools.combinations(B, 2))
    E |= {(1, x) for x in (4, 7, 8, 9)} | {(2, x) for x in (4, 7, 8, 9)} | {(3, x) for x in (4, 6, 7, 8, 9)}
    return E
def rel(e, f):
    (a, b), (c, d) = sorted([e, f])
    if len({a, b, c, d}) < 4: return "meet"
    return "separated" if b < c else "nested" if d < b else "crossing"
def strongly_nn(M):
    k = len(M); R = lambda i, j: rel(M[i], M[j])
    if any(R(i, j) in ("meet", "nested") for i, j in itertools.combinations(range(k), 2)): return False
    return all(not (R(i, j) == "crossing" and R(j, l) == "crossing") or R(i, l) == "crossing"
               for i, j, l in itertools.permutations(range(k), 3))
G = G9(); assert len(G) == 28, len(G)
for n in range(9, 13):
    if n > 9: G = G | {(i, n) for i in (1, 2, 3)}
    assert len(G) == 3 * n + 1
    bad = [M for M in itertools.combinations(sorted(G), 4) if strongly_nn(M)]
    assert not bad, (n, bad[:1])
    print(f"n={n}: {len(G)} = 3n+1 edges, no strongly non-nested 4-matching")
print("THEOREM 2 CHECKED (n = 9..12)")
