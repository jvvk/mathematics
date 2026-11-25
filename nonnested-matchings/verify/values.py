"""Certificate for every computed value stated in the note (Claude). Uses fk.py's encoding: one clause per forbidden
(strongly) non-nested k-matching on [n], plus a cardinality constraint. A value f is certified by SAT at f edges and
UNSAT at f + 1. Run: python3 values.py   (about 10 minutes)"""
import os, sys, time
CASES = [  # (k, strong, n, value) exactly as stated in the note
    *[(3, s, n, 2 * n) for s in (False, True) for n in range(6, 12)],
    *[(4, False, n, 3 * n) for n in range(8, 14)],
    (4, True, 9, 28), (4, True, 10, 31), (4, True, 11, 35), (4, True, 12, 38), (4, True, 13, 41),
    (5, False, 11, 45),
]
import fk
import os
if os.environ.get('QUICK'): CASES = [c for c in CASES if c[2] <= 11]   # mutation runs
for k, strong, n, val in CASES:
    fk.STRONG = strong; t0 = time.time()
    assert fk.solve(n, k, val) is not None, f"no graph with {val} edges (k={k}, strong={strong}, n={n})"
    assert fk.solve(n, k, val + 1) is None, f"graph with {val + 1} edges exists (k={k}, strong={strong}, n={n})"
    print(f"k={k} {'strong' if strong else 'plain '} n={n}: f = {val}  ({time.time() - t0:.0f}s)", flush=True)
print("ALL VALUES CERTIFIED")
