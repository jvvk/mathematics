"""Compare front3's exact frontier test with liar.c's direct game-tree search (independent code).

    python3 validate_front3.py      (compiles ../liar.c and front3.c into this folder)

For random positions (x0, x1, x2, x3) with small classes, liar.c gives q(x), the least number of questions. front3
must then say "winnable" at depth q(x) and "not winnable" at depth q(x) - 1 (when that depth is between 1 and 12).
Exits nonzero on any mismatch. Seed fixed, so the run is reproducible (674 comparisons on 2026-11-24)."""
import random
import subprocess
import sys

subprocess.run(["cc", "-O2", "-o", "liar", "../liar.c"], check=True)
subprocess.run(["cc", "-O2", "-o", "front3", "front3.c"], check=True)
random.seed(1)
bad = ok = 0
for trial in range(400):
    x = [random.randint(0, 12) for _ in range(4)]
    if random.random() < 0.3:
        x[3] = random.randint(0, 40)
    if sum(x) < 2:
        continue
    q = int(subprocess.run(["./liar", "3", "check", *map(str, x)], capture_output=True, text=True, check=True).stdout)
    for n in (q - 1, q):
        if n < 1 or n > 12:
            continue
        out = subprocess.run(["./front3", "12", "check", *map(str, x), str(n)], capture_output=True, text=True).stdout
        f = int(out.split()[-1])
        want = 1 if n >= q else 0
        if f != want:
            bad += 1
            print("MISMATCH", x, n, "front3", f, "liar q", q)
        else:
            ok += 1
print("comparisons", ok + bad, "agree", ok, "mismatch", bad)
sys.exit(1 if bad else 0)
