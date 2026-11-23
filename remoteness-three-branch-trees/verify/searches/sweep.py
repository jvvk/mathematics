"""Exhaustive test of Conj 4.4 over all segment multisets D with k segments and lengths <= L.
STRONG counterexample: every minimiser has >= 3 branching vertices. WEAK: some minimiser (a tie) has >= 3.
usage: python3 sweep.py k L  -> sweep_k{k}_L{L}.txt
"""

import itertools
import sys
import time

import os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from remote import remoteness_table, skeletons

k, L = int(sys.argv[1]), int(sys.argv[2])
t0 = time.time()
strong, weak, n = [], [], 0
out = open(f"sweep_k{k}_L{L}.txt", "w")
for D in itertools.combinations_with_replacement(range(L, 0, -1), k):
    tab = remoteness_table(D)
    m = min(x[0] for x in tab)
    mins = [x for x in tab if abs(x[0] - m) < 1e-9]
    nbs = sorted({x[1] for x in mins})
    n += 1
    if min(nbs) >= 3:
        strong.append((D, m, mins))
        out.write(f"STRONG {D} sigma={m} {mins}\n")
        out.flush()
    elif max(nbs) >= 3:
        weak.append((D, m, nbs))
print(
    f"k={k} L={L}: {n} sequences, {len(skeletons(k))} skeletons, strong {len(strong)}, weak(tie) {len(weak)}, "
    f"{time.time() - t0:.0f}s",
    flush=True,
)
for s in strong[:10]:
    print("STRONG", s[0], s[1], [(x[1], x[2]) for x in s[2]])
out.write(f"summary: {n} sequences, strong {len(strong)}, weak {len(weak)}\n")
