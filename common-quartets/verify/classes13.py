"""Classify the k = 3 witnesses on {inf} + Z_3 x [4] up to the maps that preserve the setup.

Leaf x in Z_13^* is written (i, j) with x = 3^i * c_j, columns c = (1, 2, 4, 7) (the orbits of x -> 3x); 0 is inf.
The three trees are T, T+1, T+2 (shift in i). Maps preserving the family: per-column shifts i -> i + s_j, column
permutations, and the inversion i -> -i (which reverses the order of the family). Order 3^4 * 24 * 2 = 3888.
"""

import sys
from itertools import permutations, product

from pysat.formula import IDPool
from pysat.solvers import Solver

sys.path.insert(0, __file__.rsplit("/", 1)[0])
from explore13 import clauses_family
from frob import decode
from quartets import splits

N, COLS = 13, (1, 2, 4, 7)
COORD = {pow(3, i, N) * c % N: (i, j) for j, c in enumerate(COLS) for i in range(3)}
INF = "inf"


def split_system(T) -> frozenset[frozenset]:
    """Nontrivial splits, each written as the side not containing inf, in grid coordinates."""
    out = set()
    for s in splits(T):
        side = s if 0 not in s else frozenset(range(N)) - s
        if 2 <= len(side) <= N - 2:
            out.add(frozenset(COORD[x] for x in side))
    return frozenset(out)


def group():
    for sh in product(range(3), repeat=4):
        for perm in permutations(range(4)):
            for e in (1, -1):
                yield lambda p, sh=sh, perm=perm, e=e: (
                    (e * p[0] + sh[p[1]]) % 3,
                    perm[p[1]],
                )


def image(S: frozenset, g) -> frozenset:
    return frozenset(frozenset(g(p) for p in side) for side in S)


def main() -> None:
    sig = [3 * x % N for x in range(N)]
    pool = IDPool()
    cls, t = clauses_family(N, 3, sig, [], pool)
    lits = list(t.values())
    wit = []
    with Solver(name="cadical153", bootstrap_with=cls) as s:
        while s.solve():
            m = set(l for l in s.get_model() if l > 0)
            wit.append(split_system(decode(N, 0, t, m)))
            s.add_clause([-v for v in lits if v in m])
    G = list(group())
    seen: set[frozenset] = set()
    classes = []
    for S in wit:
        if S in seen:
            continue
        orb = {image(S, g) for g in G}
        stab = sum(1 for g in G if image(S, g) == S)
        seen |= orb
        classes.append((S, len(orb), stab))
    print(f"{len(wit)} witnesses, {len(classes)} classes")
    for S, size, stab in sorted(classes, key=lambda c: -c[2]):
        print(f"\norbit {size}, stabiliser {stab}")
        for side in sorted(S, key=lambda x: (len(x), sorted(x))):
            print("  ", sorted(side))


if __name__ == "__main__":
    main()
