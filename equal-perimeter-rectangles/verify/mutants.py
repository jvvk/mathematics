"""Mutation test (contiguity and the 4-way-point test in valid() are implied by V + H = n - 1 plus
nonempty lines, since rooms = maximal segments + 1 + crossings; mutants removing only those survive by design)
 for recheck.py: each mutant breaks one rule; the checker must report MISMATCH
(exit 1) for every mutant on n <= 6, and pass unmutated."""
from __future__ import annotations

import os
import subprocess
import sys

SRC = open("recheck.py").read()
MUTANTS = {
    "no line checks (empty lines allowed)": ("for i in range(1, W):\n        cover = [False] * Ht", "for i in range(0):\n        cover = [False] * Ht"),
    "perimeter off by one room": ("row[n - 1] -= 1", "row[n - 1] -= 1 if rooms.index((x1, x2, y1, y2)) else 2"),
    "accept zero widths": ("r[1] <= r[0] or r[3] <= r[2]", "r[1] < r[0] or r[3] < r[2]"),
    "no reflection symmetry": ("for fx in (False, True):", "for fx in (False,):"),
}
fails = 0
base = subprocess.run([sys.executable, "-c", SRC.replace('__name__ == "__main__"', "True").replace("int(sys.argv[1]) if len(sys.argv) > 1 else 9", "6")], capture_output=True)
print("unmutated:", "PASS" if base.returncode == 0 else "FAIL")
fails += base.returncode != 0
for name, (old, new) in MUTANTS.items():
    assert SRC.count(old) == 1, name
    code = SRC.replace(old, new).replace("int(sys.argv[1]) if len(sys.argv) > 1 else 9", "6")
    r = subprocess.run([sys.executable, "-c", code], capture_output=True)
    killed = r.returncode != 0
    print(f"{name}: {'killed' if killed else 'SURVIVED'}")
    fails += not killed
if os.path.exists("noncongruent_6.json"):
    os.remove("noncongruent_6.json")  # written by the n = 6 runs
sys.exit(1 if fails else 0)
