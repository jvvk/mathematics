"""Independent recheck of the certificate base_frontiers.json (B_0..B_15).

Compiles liar.c, an exact solver that searches the two-lie game tree from the definitions of a position and a
question (it shares no code with verify_proof.py and does not use the frontier recurrence), computes each frontier
B_n(a) = largest b with (a, b, 0) winnable in n questions, and compares with the certificate. Exits 1 on any
difference. Also checks the solver against Douglas Zare's published values (MathOverflow 165093 comments)."""
import json
import subprocess
import sys
from pathlib import Path

here = Path(__file__).resolve().parent
exe = here / "liar"
subprocess.run(["cc", "-O2", "-o", str(exe), str(here / "liar.c")], check=True)

zare = [((0, 2, 50), 6), ((0, 2, 52), 7), ((2, 2, 54), 7), ((2, 2, 56), 8), ((4, 72, 0), 10), ((4, 72, 8), 10),
        ((4, 74, 0), 11)]
for x, want in zare:
    got = int(subprocess.run([str(exe), "2", "check", *map(str, x)], capture_output=True, text=True, check=True).stdout)
    if got != want:
        sys.exit(f"solver disagrees with Zare at {x}: {got} != {want}")
print("solver matches Zare's 7 values")

cert = json.loads((here / "base_frontiers.json").read_text())
assert len(cert) == 16
total = 0
for n in range(16):
    out = subprocess.run([str(exe), "2", "front", str(n)], capture_output=True, text=True, check=True).stdout
    mine = [int(t) for t in out.split()]
    if mine != cert[n]:
        sys.exit(f"MISMATCH at n = {n}")
    total += len(mine)
    print(f"n={n:2d}: {len(mine)} values agree")
assert total == 645, total
print(f"all {total} certificate values reproduced independently")

# Values printed in the paper.
table = {8: (4, 28), 9: (8, 50), 10: (16, 92), 11: (28, 170), 12: (50, 314), 13: (88, 584), 14: (154, 1092),
         15: (270, 2048)}
for n, (amax, b0) in table.items():
    if (len(cert[n]) - 1, cert[n][0]) != (amax, b0):
        sys.exit(f"Table 1 differs from the certificate at n = {n}")
print("Table 1 matches the certificate")


def need(x: tuple[int, int, int]) -> int:
    return int(subprocess.run([str(exe), "2", "check", *map(str, x)], capture_output=True, text=True,
                              check=True).stdout)


W = lambda n: 1 + n + n * (n - 1) // 2
if need((4, 0, 0)) != 8 or need((2, 2, 0)) != 7 or 2 * W(6) + 7 * 2 != 58:
    sys.exit("introduction example differs")
print("introduction example: (4,0,0) needs 8, its halving child (2,2,0) has V_6 = 58 and needs 7")
