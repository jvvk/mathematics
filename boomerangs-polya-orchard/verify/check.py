"""Checks for "Boomerangs in Polya's orchard" (MO 224015). Every claim has a mutant that must fail.

    timeout 3600 nice -n 15 python3 check.py        (about 2 minutes; needs mpmath and numpy)

C1  Theorem 1: t0 is a root of K t^2 - 2A t + r(1-r); 2(1-r)/t0 - (1-r) > 4/r - 10 for 2000 values of r in
    [1e-6, 1/3]; for 40 values of r in [1/40, 1/3] the corridor arc's exact first entry is at least that value.
C2  Table 1: every arc's exact reach (60 digits) is at least the stated value; B r^2 row; mutants.
C3  the quoted ratios: exponent 1.8 between 1/r = 10 and 20; B r / log(1/r) from 1.79 to 2.54, not monotone.
C4  the numerical upper bound U(r) r^2 = 8.6, 6.7, 6.0 at 1/r = 4, 10, 20 (bound.py).
C5  Theorem 2 constants on a grid: Q >= 2; eps_m conditions a(1 - cos eps_m) >= 1/m + 2r and tan eps_m < 2r/m for all
    m <= Q; 2a(pi/Q + epsbar) < 28/r^2; Minkowski offset <= 0.29 r.
"""
import json
import math
import pathlib
import subprocess
import sys

import mpmath as mp

HERE = pathlib.Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
from certify import reach  # noqa: E402

results = []


def report(name, good, caught):
    results.append(good and caught)
    print(f"{'PASS' if good else 'FAIL'} {name}   (mutant {'caught' if caught else 'MISSED'})", flush=True)


def t0(r, shift=1.0):
    A, K = (1 - r) ** 2, 1 - 3 * r + 3 * r * r
    return shift * r * (1 - r) / (A + mp.sqrt(A * A - K * r * (1 - r)))


def corridor(r, shift=1.0):
    t = t0(r, shift)
    alpha = 2 * mp.atan(t)
    a = (1 - r) / (1 - mp.cos(alpha))
    return a, mp.pi / 2 - alpha, 2 * (1 - r) / t - (1 - r)


# C1
mp.mp.dps = 40
ok_root = ok_ineq = True
for k in range(2000):
    r = mp.mpf(10) ** (-6 + k * (6 - mp.log10(3)) / 1999)
    A, K = (1 - r) ** 2, 1 - 3 * r + 3 * r * r
    t = t0(r)
    ok_root &= abs(K * t * t - 2 * A * t + r * (1 - r)) < mp.mpf(10) ** -30
    ok_ineq &= 2 * (1 - r) / t - (1 - r) > 4 / r - 10
ok_geo = True
for k in range(40):
    r = 1 / (3 + k * 37 / 39)
    a, th, val = corridor(mp.mpf(r), 1 + mp.mpf(10) ** -12)
    ok_geo &= reach(a, th, r, float(val) + 2) >= val - mp.mpf(10) ** -9
a, th, val = corridor(mp.mpf(1) / 8, 0.5)           # mutant: start far too steep, the disc at (0, 1) blocks
caught = reach(a, th, 1 / 8, float(val) + 2) < 2
# mutant: the bound 4/r - 9 must fail for small r
caught &= not all(2 * (1 - r) / t0(r) - (1 - r) > 4 / r - 9 for r in (mp.mpf(10) ** -k for k in range(2, 7)))
report("C1 Theorem 1: root, inequality for 2000 r, exact corridor reach for 40 r", ok_root and ok_ineq and ok_geo, caught)

# C2
r2 = subprocess.run([sys.executable, str(HERE / "certify.py")], capture_output=True, text=True, timeout=1200)
certs = json.loads((HERE / "certificates.json").read_text())
TABLE = {4: (9.909, 0.619), 5: (13.925, 0.557), 6: (18.980, 0.527), 8: (31.926, 0.498), 10: (43.793, 0.437),
         12: (65.021, 0.451), 16: (111.682, 0.436), 20: (151.995, 0.379)}
tab_ok = all(math.floor(c["reach"] * 1000) / 1000 == TABLE[int(c["inv_r"])][0]
             and math.floor(c["reach"] / c["inv_r"] ** 2 * 1000) / 1000 == TABLE[int(c["inv_r"])][1] for c in certs)
report("C2 Table 1 certified exactly (certify.py) and its rows", r2.returncode == 0 and "ALL PASS" in r2.stdout and tab_ok,
       "mutants: r + 1% loses reach on 8/8" in r2.stdout)

# C3
B = {int(c["inv_r"]): c["reach"] for c in certs}
expo = math.log(B[20] / B[10]) / math.log(2)
ratio = [B[n] / n / math.log(n) for n in sorted(B)]
good = (round(expo, 1) == 1.8 and round(ratio[0], 2) == 1.79 and round(ratio[-1], 2) == 2.54
        and any(ratio[i + 1] < ratio[i] for i in range(len(ratio) - 1)))
report(f"C3 exponent {expo:.3f}; B r/log(1/r) {ratio[0]:.3f} .. {ratio[-1]:.3f}, not monotone", good,
       round(math.log(B[20] / B[8]) / math.log(2.5), 1) != 1.8)

# C4
outs = {}
for inv in (4, 10, 20):
    o = subprocess.run([sys.executable, str(HERE / "bound.py"), str(inv)], capture_output=True, text=True, timeout=900)
    outs[inv] = float(o.stdout.split("U*r^2=")[1].split()[0])
report(f"C4 numerical U r^2 {outs}", round(outs[4], 1) == 8.6 and round(outs[10], 1) == 6.7 and round(outs[20], 1) == 6.0,
       round(outs[20], 1) != 5.0)


# C5
def middle_ok(fac):
    ok = True
    for r in (0.1, 0.05, 0.02, 0.01):
        lo, hi = 2 / r ** 2, 4 / r ** 3
        for k in range(1, 60):
            a = lo * (hi / lo) ** (k / 60)
            Q = min(a * r * r, math.sqrt(a * r) / 2)
            ok &= Q >= 2
            for m in [1 + (Q - 1) * i / 50 for i in range(51)]:
                e = fac * math.sqrt(2 * (1 / m + 2 * r) / a)
                ok &= a * (1 - math.cos(e)) >= 1 / m + 2 * r and math.tan(e) < 2 * r / m
            eb = 1.01 * math.sqrt(2 * (1 + 2 * r) / a)
            ok &= 2 * a * (math.pi / Q + eb) < 28 / r ** 2
        for t in [3 / (2 * r) * i / 20 for i in range(21)]:
            a = 4 / r ** 3
            ok &= a - math.sqrt(a * a - t * t) <= 0.29 * r
    return ok


report("C5 Theorem 2 constants on a grid", middle_ok(1.01), not middle_ok(0.99))
print("ALL PASS" if all(results) else "SOME FAIL")
sys.exit(0 if all(results) else 1)
