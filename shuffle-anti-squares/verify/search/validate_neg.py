"""Negative-side validation: known anti-squares must be UNSAT for every rotation; their mutants must agree with brute force.
Exits 1 on any mismatch and 3 if the solver or ./antisq is inconclusive."""
import sys

from classes import canon
from ilp_proof import Inconclusive, circ_gaps, run_antisq, some_rotation_is_square

ws = sorted({canon(l.strip()) for l in open("../results/anti_26.txt") if l.strip()})
if len(ws) != 26:
    sys.exit(f"expected the 26 classes of length 26, read {len(ws)}")
muts = []
for w in ws[:10]:
    for i in range(len(w)):
        for j in range(i + 1, len(w)):
            if w[i] != w[j]:
                m = list(w); m[i], m[j] = m[j], m[i]; muts.append("".join(m))
muts = sorted(set(muts) - set(ws))[:300]
try:
    brute = run_antisq(ws + muts)
    if not all(brute[w] for w in ws):
        sys.exit("brute force does not confirm the listed anti-squares")
    bad = [w for w in ws + muts if (not some_rotation_is_square(circ_gaps(w))[0]) != brute[w]]
except Inconclusive as e:
    print("INCONCLUSIVE:", e, file=sys.stderr)
    sys.exit(3)
print(f"{len(ws)} anti-squares + {len(muts)} mutants ({sum(brute[m] for m in muts)} anti) checked, mismatches {len(bad)}")
for w in bad:
    print("MISMATCH", w)
sys.exit(1 if bad else 0)
