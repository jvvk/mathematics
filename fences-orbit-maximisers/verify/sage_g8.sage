# Independent recomputation of g(n), n <= 8, with Sage's own poset generator and counters; asserts agreement with
# Theorem 1 (values, number of maximisers, and the maximisers up to isomorphism) and the facts about R.
# Run: sage sage_g8.sage   (prints ALL PASS, exits nonzero otherwise)
import sys
G = {1: 1, 2: 1, 3: 3, 4: 6, 5: 25, 6: 75, 7: 525, 8: 2384}
def fence(m):
    return Poset((list(range(m)), [(i, i + 1) if i % 2 == 0 else (i + 1, i) for i in range(m - 1)]))
pt = Poset(([0], []))
def plus(*ps):
    out = ps[0]
    for p in ps[1:]:
        out = out.disjoint_union(p)
    return out
Q = Poset((list('abcdefg'), [('a','b'),('c','b'),('c','d'),('e','d'),('e','f'),('g','d')]))
R = Poset((list('abcdefgh'), [('a','b'),('c','b'),('c','d'),('e','d'),('e','f'),('g','d'),('c','h')]))
WANT = {1: [pt], 2: [fence(2), plus(pt, pt)], 3: [plus(fence(2), pt)], 4: [plus(fence(2), pt, pt)],
        5: [plus(fence(4), pt)], 6: [plus(fence(2), fence(4)), plus(fence(4), pt, pt)],
        7: [plus(fence(2), fence(4), pt)], 8: [plus(Q, pt), plus(Q.dual(), pt)]}
ok = True
for n in range(1, 9):
    best = 0; arg = []
    for P in Posets(n):
        f = P.linear_extensions().cardinality() / P.hasse_diagram().automorphism_group().order()
        if f > best: best, arg = f, [P]
        elif f == best: arg.append(P)
    same = best == G[n] and len(arg) == len(WANT[n]) and all(any(P.is_isomorphic(W) for P in arg) for W in WANT[n])
    ok = ok and same
    print(n, best, len(arg), "OK" if same else "DIFFERENT"); sys.stdout.flush()
eR = R.linear_extensions().cardinality(); aR = R.hasse_diagram().automorphism_group().order()
eQ = Q.linear_extensions().cardinality(); aQ = Q.hasse_diagram().automorphism_group().order()
facts = (eQ, aQ, eR, aR, R.is_isomorphic(R.dual()), Q.is_isomorphic(Q.dual())) == (298, 1, 1613, 1, True, False)
ok = ok and facts
print('e(Q), aut, e(R), aut, R self-dual, Q self-dual:', eQ, aQ, eR, aR, R.is_isomorphic(R.dual()), Q.is_isomorphic(Q.dual()))
print("ALL PASS" if ok else "FAILED")
sys.exit(int(0 if ok else 1))  # int(): Sage would pass its own Integer, which exits 1
