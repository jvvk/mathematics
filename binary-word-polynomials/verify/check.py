"""Checks for "Binary words with the same characteristic polynomial" (MO 514920). Every claim has a mutant that must
fail.

    timeout 3600 nice -n 15 ~/.venvs/main/bin/python check.py [--full]   (default about 10 minutes; --full adds the
                                                                          remaining soundness mutants, about 30 more)

C1  enum.c gives a_n for n <= 22 as in the note, agreeing with Weiss's terms for n <= 15.
C2  every fingerprint class of reversal pairs is one class of exact integer polynomials.
C3  the census table: classes, unexplained classes, the three-pair class at n = 18, totals 822 and 805.
C4  every block-reversal move used by the census (333) is confirmed exactly over Q(t).
C5  the kinds of move: 123 interleavings, 56 with an equal-diagonal G, 154 other.
C6  soundness: exhaustively for n <= 8, the search never accepts a move between words with different polynomials.
C7  the facts quoted in the text: the question's polynomial, the displayed coincidences, the n = 13 matrix G and
    lambda, the irreducible degree-9 polynomial, the excess ratio bounds, and Theorem R failing for equal end letters.
"""

from __future__ import annotations

import random
import subprocess
import sys
from pathlib import Path

import sympy as sp

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
FULL = "--full" in sys.argv
OUT = HERE / "out"
OUT.mkdir(exist_ok=True)

A_NOTE = [
    2,
    3,
    6,
    10,
    20,
    36,
    72,
    134,
    270,
    526,
    1052,
    2072,
    4154,
    8231,
    16504,
    32856,
    65764,
    131249,
    262604,
    524606,
    1049560,
    2097843,
]
A_WEISS = A_NOTE[:15]
TABLE = {
    8: (2, 0),
    9: (2, 2),
    10: (2, 0),
    11: (4, 0),
    12: (8, 0),
    13: (6, 2),
    14: (25, 0),
    15: (8, 0),
    16: (40, 0),
    17: (28, 2),
    18: (78, 1),
    19: (52, 4),
    20: (194, 2),
    21: (40, 0),
    22: (333, 4),
}  # n: (classes, unexplained)
results: list[bool] = []


def report(name: str, good: bool, caught: bool) -> None:
    results.append(good and caught)
    print(
        f"{'PASS' if good else 'FAIL'} {name}   (mutant {'caught' if caught else 'MISSED'})",
        flush=True,
    )


def enum_counts(flags: list[str], write: bool) -> list[int]:
    exe = HERE / ("enum_chk" if not flags else "enum_mut")
    subprocess.run(
        ["cc", "-O2", *flags, "-o", str(exe), str(HERE / "enum.c")], check=True
    )
    a = []
    for n in range(1, 23):
        r = subprocess.run(
            [str(exe), str(n)], capture_output=True, text=True, check=True, timeout=600
        )
        a.append(int(r.stderr.split("a_n=")[1]))
        if write:
            (OUT / f"c{n}.txt").write_text(r.stdout)
    exe.unlink()
    return a


# C1
a = enum_counts([], write=True)
a_mut = enum_counts(["-DMUT_SHORTFP"], write=False)
report(
    "C1 a_n for n <= 22 as in the note; n <= 15 as in the question",
    a == A_NOTE and a[:15] == A_WEISS,
    a_mut != A_NOTE,
)

import classify as C
import exact as E


# C2
def fp_classes_exact(charpoly) -> bool:
    for n in range(1, 23):
        for line in (OUT / f"c{n}.txt").read_text().splitlines():
            ws = line.split()[1:]
            if len({charpoly(w) for w in ws}) != 1:
                return False
    return True


bad_poly = lambda w: E.charpoly(w[:-1] + "0")  # mutant: ignores the last letter
report(
    "C2 every fingerprint class is a single exact class",
    fp_classes_exact(E.charpoly),
    not fp_classes_exact(bad_poly),
)


# C3
def census_table() -> tuple[dict, int]:
    tab, three = {}, 0
    for n in range(8, 23):
        res, left = C.census(n)
        tab[n] = (res["fibres"], len(left))
        three += sum(1 for g in E.classes(n) if len(g) == 3 and n == 18)
    return tab, three


tab, three = census_table()
good = (
    tab == TABLE
    and three == 1
    and sum(c for c, _ in tab.values()) == 822
    and sum(c - u for c, u in tab.values()) == 805
)
C.MUT.add("--mut-noboundary")
tab_mut = {n: (C.census(n)[0]["fibres"], len(C.census(n)[1])) for n in (9, 13)}
C.MUT.discard("--mut-noboundary")
report(
    "C3 census table, 822 classes, 805 explained, one three-pair class at n = 18",
    good,
    tab_mut != {9: TABLE[9], 13: TABLE[13]},
)

# C4
import exactcheck as X

tot = conf = 0
for n in range(8, 23):
    e, c, _ = X.edges(n)
    tot += e
    conf += c
# mutant: the n = 13 move with a different right-hand context must not be confirmed
caught = X.confirm("1101011000101", "1100010101100", 1, 3, 1, [0, 5, 9]) is False
report(
    f"C4 all {tot} block-reversal moves confirmed exactly",
    tot == 333 and conf == 333,
    caught,
)

# C5
import gtypes as K

tot5 = {"I": 0, "R": 0, "N": 0}
for n in range(8, 23):
    cnt, _ = K.kinds(n)
    for k in tot5:
        tot5[k] += cnt[k]
cnt_mut = {"I": 0, "R": 0, "N": 0}
for n in (13, 16):
    cnt, _ = K.kinds(
        n, eq=(0, 0, 0)
    )  # mutant: no equal-diagonal condition, every move counts as R
    for k in cnt_mut:
        cnt_mut[k] += cnt[k]
report(f"C5 kinds {tot5}", tot5 == {"I": 123, "R": 56, "N": 154}, cnt_mut["N"] == 0)


# C6
def sound(n: int, *mut: str) -> tuple[int, int]:
    r = subprocess.run(
        [sys.executable, str(HERE / "soundtest.py"), str(n), *mut],
        capture_output=True,
        text=True,
        cwd=HERE,
        timeout=3600,
    )
    w = r.stdout.split()
    return int(w[w.index("nontrivial") + 1]), int(w[w.index("false") + 1])


nt, fl = sound(8)
muts = ["--mut-nolam"] + (["--mut-noboundary", "--mut-noblocks"] if FULL else [])
caught = all(sound(8, m)[1] > 0 for m in muts)
report(
    f"C6 exhaustive soundness n <= 8: 0 false acceptances, {nt} nontrivial ({', '.join(muts)} caught)",
    fl == 0 and nt > 0,
    caught,
)

# C7
t = sp.symbols("t")
P = lambda w: sp.Poly(list(reversed(E.charpoly(w))), t)
facts = []
facts.append(
    P("00011011")
    == P("00100111")
    == sp.Poly(
        t**8
        - 4 * t**7
        - t**6
        + 17 * t**5
        - 7 * t**4
        - 19 * t**3
        + 9 * t**2
        + 4 * t
        - 1,
        t,
    )
)
for u, v in [
    ("10110010", "10010110"),
    ("101001100000", "101100001000"),
    ("1101011000101", "1100010101101"),
    ("1101111000101", "1100010111101"),
    ("111010100", "100110110"),
    ("110101000", "100100110"),
]:
    facts.append(P(u) == P(v) and v not in (u, u[::-1]))
al = (t**3 - 2 * t**2 - t + 1) * (t**3 - 2 * t**2 - t + 3)
be = (t - 1) * (t**4 - 2 * t**3 - 2 * t**2 + 3 * t + 1)
ga = t * (t - 2) * (t**2 - 2)
lam = t**4 - 3 * t**3 + 4 * t - 1


def g_ok(al, be, ga, lam) -> bool:
    G = sp.Matrix([[al, be], [be, ga]])
    ok = True
    for Y in ("10101", "1000", "10111"):
        Z = X.M(Y) * G
        ok &= sp.expand(Z[0, 1] - Z[1, 0]) == 0
    xA, yB = X.M("1")[0, :].T, X.M("101")[:, 0]
    ok &= sp.expand(G * xA - lam * yB) == sp.zeros(2, 1)
    return ok and sp.expand(G.det()) != 0


facts.append(g_ok(al, be, ga, lam))
facts.append(
    sp.Poly(P("111010100").as_expr(), t).is_irreducible and P("111010100").degree() == 9
)
r = lambda n: (2**n + 2 ** ((n + 1) // 2)) // 2
ratios = [(r(n) - a[n - 1]) / 2 ** (n / 2) for n in range(8, 23)]
facts.append(0.02 <= min(ratios) and max(ratios) <= 0.2)
# Theorem R with equal end letters fails in random trials
rng = random.Random(5)
trials = fails = 0
flip = lambda c: "1" if c == "0" else "0"
while trials < 60:
    X0 = "".join(rng.choice("01") for _ in range(rng.randint(3, 6)))
    if X0[0] != X0[-1] or X0 == X0[::-1]:
        continue
    Ys = [rng.choice([X0, X0[::-1]]) for _ in range(rng.randint(2, 4))]
    A, B = flip(X0[0]) + X0[1:], X0[:-1] + flip(X0[-1])
    u, v = A + "".join(Ys) + B, A + "".join(Ys[::-1]) + B
    if u in (v, v[::-1]):
        continue
    trials += 1
    fails += E.charpoly(u) != E.charpoly(v)
facts.append(fails == trials)
caught = not g_ok(al, be, ga, lam + 1) and P("10110010") != P("10010111")
report(
    f"C7 facts quoted in the text ({sum(facts)}/{len(facts)}; R with equal end letters fails {fails}/{trials})",
    all(facts),
    caught,
)

print("ALL PASS" if all(results) else "SOME FAIL")
sys.exit(0 if all(results) else 1)
