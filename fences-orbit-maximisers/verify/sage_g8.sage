# Independent recomputation of g(n) with Sage's own poset generator and counters.
import sys
for n in range(1, 9):
    best = 0; arg = []
    for P in Posets(n):
        f = P.linear_extensions().cardinality() / P.hasse_diagram().automorphism_group().order()
        if f > best: best, arg = f, [P]
        elif f == best: arg.append(P)
    print(n, best, len(arg), [sorted(Q.cover_relations()) for Q in arg]); sys.stdout.flush()
R = Poset((list('abcdefgh'), [('a','b'),('c','b'),('c','d'),('e','d'),('e','f'),('g','d'),('c','h')]))
print('e(R) =', R.linear_extensions().cardinality(), 'aut', R.hasse_diagram().automorphism_group().order(), 'selfdual', R.is_isomorphic(R.dual()))
