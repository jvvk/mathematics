"""Independent recheck (shares no code with fk.py / values.py): recomputes the same values by a different enumeration
of forbidden matchings (k-subsets of edges filtered by pairwise relations computed from sorted endpoints).
Run: python3 recheck_values.py   (about 15 minutes)"""
import sys
if not __debug__: sys.exit("run without -O: the checks are assert statements")

import itertools, time
from pysat.solvers import Minisat22
from pysat.card import CardEnc, EncType
from pysat.formula import IDPool

def relation(e, f):
    a, b = e; c, d = f
    if a > c: a, b, c, d = c, d, a, b
    if len({a, b, c, d}) < 4: return "meet"
    if b < c: return "separated"
    if d < b: return "nested"
    return "crossing"

def forbidden(n, k, strong):
    E = list(itertools.combinations(range(1, n + 1), 2))
    for M in itertools.combinations(E, k):
        R = {(i, j): relation(M[i], M[j]) for i, j in itertools.combinations(range(k), 2)}
        if any(r in ("meet", "nested") for r in R.values()): continue
        if strong:
            cr = lambda i, j: i != j and R[(min(i, j), max(i, j))] == "crossing"
            if any(cr(i, j) and cr(j, l) and not cr(i, l) for i in range(k) for j in range(k) for l in range(k) if i != l):
                continue
        yield M

def feasible(n, k, strong, m, F):
    pool = IDPool(); E = list(itertools.combinations(range(1, n + 1), 2)); v = {e: pool.id(e) for e in E}
    cls = [[-v[e] for e in M] for M in F] + CardEnc.atleast([v[e] for e in E], bound=m, vpool=pool, encoding=EncType.totalizer).clauses
    with Minisat22(bootstrap_with=cls) as s: return s.solve()

CASES = [*[(3, s, n, 2 * n) for s in (False, True) for n in range(6, 12)],
         *[(4, False, n, 3 * n) for n in range(8, 14)],
         (4, True, 9, 28), (4, True, 10, 31), (4, True, 11, 35), (4, True, 12, 38), (4, True, 13, 41), (5, False, 11, 45)]
import os
if '--quick' in sys.argv: CASES = [c for c in CASES if c[2] <= 11]   # mutation runs
for k, strong, n, val in CASES:
    t0 = time.time(); F = list(forbidden(n, k, strong))
    assert feasible(n, k, strong, val, F) and not feasible(n, k, strong, val + 1, F), (k, strong, n, val)
    print(f"k={k} {'strong' if strong else 'plain '} n={n}: f = {val}  ({time.time() - t0:.0f}s)", flush=True)
print("ALL VALUES RECHECKED")
