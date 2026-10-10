"""Checks for "Rectangles from all hole-free n-ominoes: parity" (MO 378923). Every claim has a mutant that must fail.

    timeout 900 nice -n 15 ~/.venvs/main/bin/python check.py [--full]     (--full adds n = 16, about 3 minutes)

P1  parity.c reproduces OEIS A001168 (fixed), A000105 (free) and A000104 (free without holes) for n <= 14 (16).
P2  for n <= 10 an independent pure-Python enumeration (free shapes grown cell by cell, own hole test) gives the
    same hole-free counts and the same imbalance sum S(n) = sum |black - white|.
P3  the table of S(n) in the note, and S(n) mod 4 = 2 exactly for n = 4, 6, 8, 10, 16 among even n <= 16.
P4  no obstruction where the note says so: for n = 12, 14 (even) a signed sum of the imbalances can be 0, and for
    odd n <= 15 it can be 0 or 1 as the rectangle requires (subset sums over the histogram).
"""

from __future__ import annotations

import re
import subprocess
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
FULL = "--full" in sys.argv
NMAX = 16 if FULL else 14
A001168 = [0, 1, 2, 6, 19, 63, 216, 760, 2725, 9910, 36446, 135268, 505861, 1903890, 7204874, 27394666, 104592937]
A000105 = [0, 1, 1, 2, 5, 12, 35, 108, 369, 1285, 4655, 17073, 63600, 238591, 901971, 3426576, 13079255]
A000104 = [0, 1, 1, 2, 5, 12, 35, 107, 363, 1248, 4460, 16094, 58937, 217117, 805475, 3001127, 11230003]
S_NOTE = {4: 2, 5: 14, 6: 22, 7: 123, 8: 278, 9: 1502, 10: 4010, 11: 20462, 12: 59248, 13: 291211, 14: 886436,
          15: 4231527, 16: 13329078}
results: list[bool] = []


def report(name: str, good: bool, caught: bool) -> None:
    results.append(good and caught)
    print(f"{'PASS' if good else 'FAIL'} {name}   (mutant {'caught' if caught else 'MISSED'})", flush=True)


def build(flags: list[str], out: str) -> Path:
    exe = HERE / out
    subprocess.run(["cc", "-O2", *flags, "-o", str(exe), str(HERE / "parity.c")], check=True)
    return exe


def run(exe: Path, n: int) -> dict:
    out = subprocess.run([str(exe), str(n)], capture_output=True, text=True, check=True, timeout=1200).stdout
    m = re.search(r"fixed=(\d+) free=(\d+) free_holefree=(\d+) sum_c=(\d+)", out)
    hist = {int(a): int(b) for a, b in re.findall(r"(\d+):(\d+)", out.split("hist:")[1])}
    return dict(fixed=int(m[1]), free=int(m[2]), hf=int(m[3]), S=int(m[4]), hist=hist)


def oeis_ok(r: dict, n: int) -> bool:
    return r["fixed"] == A001168[n] and r["free"] == A000105[n] and r["hf"] == A000104[n]


exe = build([], "parity_chk")
res = {n: run(exe, n) for n in range(1, NMAX + 1)}

# P1
mut_nostab, mut_holes = build(["-DMUT_NOSTAB"], "parity_m1"), build(["-DMUT_HOLES"], "parity_m2")
caught = not oeis_ok(run(mut_nostab, 8), 8) and not oeis_ok(run(mut_holes, 8), 8)
report(f"P1 counts match A001168, A000105, A000104 for n <= {NMAX}", all(oeis_ok(res[n], n) for n in res), caught)


# P2 independent Python enumeration
def grow_free(n: int) -> set:
    def canon(cells):
        best = None
        for t in range(8):
            pts = []
            for x, y in cells:
                p, q = (y, x) if t & 4 else (x, y)
                pts.append((-p if t & 1 else p, -q if t & 2 else q))
            mx, my = min(p for p, _ in pts), min(q for _, q in pts)
            c = tuple(sorted((p - mx, q - my) for p, q in pts))
            best = c if best is None or c < best else best
        return best

    level = {((0, 0),)}
    for _ in range(n - 1):
        nxt = set()
        for s in level:
            cs = set(s)
            for x, y in s:
                for d in ((x + 1, y), (x - 1, y), (x, y + 1), (x, y - 1)):
                    if d not in cs:
                        nxt.add(canon(cs | {d}))
        level = nxt
    return level


def holes(s) -> bool:
    cs = set(s)
    W, H = max(x for x, _ in s) + 1, max(y for _, y in s) + 1
    seen, stack = {(-1, -1)}, [(-1, -1)]
    while stack:
        x, y = stack.pop()
        for d in ((x + 1, y), (x - 1, y), (x, y + 1), (x, y - 1)):
            if -1 <= d[0] <= W and -1 <= d[1] <= H and d not in cs and d not in seen:
                seen.add(d)
                stack.append(d)
    return len(seen) + len(cs) != (W + 2) * (H + 2)


def py_stats(n: int, colour=lambda x, y: (x + y) % 2) -> tuple[int, int]:
    hf = [s for s in grow_free(n) if not holes(s)]
    return len(hf), sum(abs(sum(1 if colour(x, y) else -1 for x, y in s)) for s in hf)


good = all(py_stats(n) == (res[n]["hf"], res[n]["S"]) for n in range(1, 11))
# the figure: exactly three octominoes have imbalance 4, the largest; they are the three drawn
FIG = [[(0, 0), (0, 1), (0, 2), (1, 1), (2, 0), (2, 1), (2, 2), (3, 1)],
       [(0, 1), (0, 3), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, 1)],
       [(0, 1), (1, 0), (1, 1), (1, 2), (2, 1), (2, 2), (2, 3), (3, 2)]]
imb8 = {s: abs(sum(1 if (x + y) % 2 else -1 for x, y in s)) for s in grow_free(8) if not holes(s)}
canon_fig = set()
for cells in FIG:
    canon_fig |= {s for s in imb8 if sorted(s) == sorted(cells)} or {None}
good &= max(imb8.values()) == 4 and {s for s, c in imb8.items() if c == 4} == canon_fig
good &= res[8]["hist"] == {0: 227, 2: 133, 4: 3}
caught = py_stats(8, colour=lambda x, y: x % 2) != (res[8]["hf"], res[8]["S"])
report("P2 independent Python enumeration agrees for n <= 10; the figure's three octominoes", good, caught)

# P3
good = all(res[n]["S"] == S_NOTE[n] for n in res if n >= 4)
dec = {n for n in res if n % 2 == 0 and n >= 2 and res[n]["S"] % 4 == 2}
good &= dec == ({4, 6, 8, 10, 16} if FULL else {4, 6, 8, 10})
caught = run(build(["-DMUT_STRIPE"], "parity_m3"), 8)["S"] != S_NOTE[8]
report("P3 the note's table of S(n); S(n) = 2 mod 4 exactly for n = 4, 6, 8, 10" + (", 16" if FULL else ""), good, caught)


# P4 subset sums
def signed_sums(hist: dict) -> set:
    sums = {0}
    for c, m in hist.items():
        for _ in range(m if c else 0):
            sums = {s + c for s in sums} | {s - c for s in sums}
            if len(sums) > 200:  # only small targets matter; keep the window bounded
                sums = {s for s in sums if abs(s) <= 100}
    return sums


def feasible(n: int, r: dict) -> bool:
    N = r["hf"]
    small = {c: min(m, 60) for c, m in r["hist"].items()}  # 60 copies of each value already reach every small target
    sums = signed_sums(small)
    rest = {c: m - small[c] for c, m in r["hist"].items()}
    # the remaining copies come in pairs (+c, -c) when their number is even; an odd leftover is shifted by one c
    shift = sum(c for c, m in rest.items() if m % 2)
    targets = {0} if (n * N) % 2 == 0 else {1, -1}
    return any((t - shift) in sums or (t + shift) in sums for t in targets)


good = all(feasible(n, res[n]) for n in res if n >= 5 and (n % 2 == 1 or n in (12, 14)))
caught = not feasible(8, res[8])
report("P4 no checkerboard obstruction for n = 12, 14 and odd n", good, caught)

for f in ("parity_chk", "parity_m1", "parity_m2", "parity_m3"):
    (HERE / f).unlink(missing_ok=True)
print("ALL PASS" if all(results) else "SOME CHECK FAILED")
sys.exit(0 if all(results) else 1)
