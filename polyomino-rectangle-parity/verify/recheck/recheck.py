"""Independent recheck (shares no code with ../check.py or ../parity.c): grow.c builds free polyominoes level by level
with a hash set and recomputes the hole-free counts and imbalance sums S(n) stated in the note.

    timeout 1800 nice -n 15 ~/.venvs/main/bin/python recheck.py [--full]     (--full adds n = 15, 16: about 5 minutes)
"""

from __future__ import annotations

import re
import subprocess
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
NMAX = 16 if "--full" in sys.argv else 14
HOLEFREE = {4: 5, 5: 12, 6: 35, 7: 107, 8: 363, 9: 1248, 10: 4460, 11: 16094, 12: 58937, 13: 217117, 14: 805475,
            15: 3001127, 16: 11230003}
S = {4: 2, 5: 14, 6: 22, 7: 123, 8: 278, 9: 1502, 10: 4010, 11: 20462, 12: 59248, 13: 291211, 14: 886436,
     15: 4231527, 16: 13329078}


def build(flags: list[str], out: str) -> Path:
    exe = HERE / out
    subprocess.run(["cc", "-O2", *flags, "-o", str(exe), str(HERE / "grow.c")], check=True)
    return exe


def stats(exe: Path, n: int) -> tuple[int, int]:
    out = subprocess.run([str(exe), str(n)], capture_output=True, text=True, check=True, timeout=1800).stdout
    m = re.search(r"free_holefree=(\d+) sum_c=(\d+)", out)
    return int(m[1]), int(m[2])


exe = build([], "grow_chk")
bad = [n for n in range(4, NMAX + 1) if stats(exe, n) != (HOLEFREE[n], S[n])]
for n in range(4, NMAX + 1):
    print(f"n={n}: hole-free {HOLEFREE[n]}, S = {S[n]}, S mod 4 = {S[n] % 4}", flush=True)
mut = build(["-DMUT_STRIPE"], "grow_mut")
caught = stats(mut, 8) != (HOLEFREE[8], S[8])
for f in ("grow_chk", "grow_mut"):
    (HERE / f).unlink(missing_ok=True)
if bad:
    sys.exit(f"FAIL at n = {bad}")
if not caught:
    sys.exit("UNDETECTED MUTANT: stripe colouring")
print(f"recheck: all counts and sums agree for n <= {NMAX}; rejected mutant: stripe colouring")
