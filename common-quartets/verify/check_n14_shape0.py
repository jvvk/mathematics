"""Fast regression for the n = 14 search: shape 0 must be UNSAT and the n = 13 instance SAT (used by mutants.py)."""
import sys
from itertools import combinations

from pysat.formula import IDPool
from pysat.solvers import Solver

sys.path.insert(0, __file__.rsplit("/", 1)[0])
from quartets import quartet_map  # noqa: E402
from sat_h3 import encode, split_index  # noqa: E402
from shapes import unrooted  # noqa: E402

# The ban must cover all three split types: this 6-leaf triple shares exactly one quartet, of type ad|bc (index 2).
pool = IDPool()
fixed = [(0, (1, ((2, 4), (3, 5)))), (0, ((((1, 5), 2), 3), 4)), (0, ((1, ((2, 4), 5)), 3))]
units = []
for t, tr in enumerate(fixed):
    qm = quartet_map(tr)
    units += [[pool.id(("x", t, Q, split_index(Q, qm[frozenset(Q)])))] for Q in combinations(range(6), 4)]
with Solver(name="cadical153", bootstrap_with=encode(6, 3, pool) + units) as s:
    assert not s.solve(), "a triple with a common ad|bc quartet must be rejected"
pool = IDPool()
base = encode(13, 3, pool)
with Solver(name="cadical153", bootstrap_with=base) as s:
    assert s.solve(), "n = 13 must be SAT"
n = 14
assert len(unrooted(n)) == 135, "A000672(14) = 135"
pool = IDPool()
base = encode(n, 3, pool)
t = unrooted(n)[0]
qm = quartet_map(t)
units = [[pool.id(("x", 0, Q, split_index(Q, qm[frozenset(Q)])))] for Q in combinations(range(n), 4)]
with Solver(name="cadical153", bootstrap_with=base + units) as s:
    assert not s.solve(), "n = 14 shape 0 must be UNSAT"
print("ok: n=13 SAT, 135 shapes, n=14 shape 0 UNSAT")
