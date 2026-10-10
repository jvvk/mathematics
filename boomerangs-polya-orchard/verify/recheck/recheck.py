"""Independent recheck (shares no code with ../): dense sampling of each certified arc and of corridor arcs.

For every arc in ../certificates.json, and for the corridor arc of Theorem 1 at r = 1/3, 1/4, ..., 1/30 (built here
from its own formula), sample 400,000 points up to the stated reach and measure the distance to the nearest
nonzero lattice point; it must be at least r (up to 1e-7, tangencies). Mutant: discs 10% larger must be entered
(the corridor arc at r = 1/3 keeps 4.5% slack up to its proven reach, so 1% is too small there).

    python3 recheck.py   -> ALL AGREE / DISAGREE
"""
import json
import math
import pathlib
import sys

from check_arc import clearance_profile

HERE = pathlib.Path(__file__).resolve().parent
certs = json.loads((HERE.parent / "certificates.json").read_text())


def corridor(r):
    A, K = (1 - r) ** 2, 1 - 3 * r + 3 * r * r
    t = r * (1 - r) / (A + math.sqrt(A * A - K * r * (1 - r))) * (1 + 1e-12)
    alpha = 2 * math.atan(t)
    a = (1 - r) / (1 - math.cos(alpha))
    return a, math.pi / 2 - alpha, 2 * (1 - r) / t - (1 - r)


arcs = [(1 / c["inv_r"], c["a"], c["theta"], c["reach"]) for c in certs]
arcs += [(1 / k, *corridor(1 / k)) for k in range(3, 31)]
ok, worst, mut = True, 1.0, 0
for r, a, th, R in arcs:
    s, cl = clearance_profile(a, th, min(2 * a, R))
    m = cl.min()
    ok &= m >= r - 1e-7
    worst = min(worst, m - r)
    mut += cl.min() < 1.10 * r
print(f"{len(arcs)} arcs: min clearance - r = {worst:.2e}; with discs 10% larger, {mut}/{len(arcs)} arcs are entered")
ok &= mut == len(arcs)
print("ALL AGREE" if ok else "DISAGREE")
sys.exit(0 if ok else 1)
