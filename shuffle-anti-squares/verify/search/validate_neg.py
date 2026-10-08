"""Negative-side validation: known anti-squares must be UNSAT for every rotation; their mutants must agree with brute force."""
import subprocess
from classes import canon
from ilp_proof import circ_gaps, some_rotation_is_square

ws = sorted({canon(l.strip()) for l in open("../results/anti_26.txt") if l.strip()})
muts = []
for w in ws[:10]:
    for i in range(len(w)):
        for j in range(i + 1, len(w)):
            if w[i] != w[j]:
                m = list(w); m[i], m[j] = m[j], m[i]; muts.append("".join(m))
muts = sorted(set(muts))[:300]
out = subprocess.run(["./antisq"], input="\n".join(ws + muts) + "\n", capture_output=True, text=True).stdout.split()
brute = dict(zip(out[1::2], (v == "1" for v in out[0::2])))
bad = sum((not some_rotation_is_square(circ_gaps(w))[0]) != brute[w] for w in ws + muts)
print(f"{len(ws)} anti-squares + {len(muts)} mutants ({sum(brute[m] for m in muts)} anti) checked, mismatches {bad}")
