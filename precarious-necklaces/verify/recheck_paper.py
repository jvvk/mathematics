"""Independent recheck of every finite claim in paper/precarious-necklaces.tex.

Shares no code with the other scripts in verify/: words are tested for being proper powers by
comparing with repetitions of a prefix, the constructions are rebuilt from the paper's own
description in Section 3, and Table 1 is parsed from the .tex. Run from verify/:

    python3 recheck_paper.py          # a few seconds
    MUTANT=1 python3 recheck_paper.py # plants an error in the even construction; must end in FAIL
"""
from __future__ import annotations

import itertools
import math
import os
import re
import sys
from pathlib import Path

TEX = Path(__file__).resolve().parent.parent / "paper" / "precarious-necklaces.tex"
PRIMES = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29]
MUTANT = os.environ.get("MUTANT") == "1"
failures: list[str] = []


def check(ok: bool, what: str) -> None:
    print(("ok   " if ok else "FAIL ") + what)
    if not ok:
        failures.append(what)


def primorial(m: int) -> int:
    return math.prod(PRIMES[:m])


def power_exponents(w: str) -> list[int]:
    """All r >= 2 with w = v^r."""
    n = len(w)
    return [r for r in range(2, n + 1) if n % r == 0 and w == w[: n // r] * r]


def symmetric(w: str) -> bool:
    """Lemma 1: a necklace is symmetric iff a representing word is a proper power."""
    return bool(power_exponents(w))


def keep(w: str, S) -> str:
    return "".join(c for c in w if c in S)


def s_precarious(w: str, s: int) -> bool:
    cols = sorted(set(w))
    return (not symmetric(w)) and all(
        symmetric(keep(w, S)) for S in itertools.combinations(cols, s)
    )


def precarious(w: str) -> bool:
    cols = set(w)
    return len(cols) >= 2 and s_precarious(w, len(cols) - 1)


def closed(k: int, s: int) -> int:
    return s * primorial(s // 2 + 1) + (k - s) * primorial((s + 1) // 2)


def a(k: int) -> int:
    m = k // 2
    return 2 * m * primorial(m) if k % 2 == 0 else primorial(m) * (2 * m * PRIMES[m] + 1)


LETTERS = "abcdefghijklmnop"


def pair_block(h: int, j: int) -> str:
    """Block j: pair i as x_i y_i if p_i divides j, else y_i x_i (Section 3)."""
    out = []
    for i in range(h):
        x, y = LETTERS[2 * i], LETTERS[2 * i + 1]
        out.append(x + y if j % PRIMES[i] == 0 else y + x)
    return "".join(out)


def construction(k: int, s: int) -> str:
    if s % 2 == 1:
        h = s // 2
        fixed = LETTERS[2 * h + 2 : k]
        return "".join(pair_block(h + 1, j) + fixed for j in range(primorial(h + 1)))
    h = s // 2
    cluster = LETTERS[2 * h : k]
    q = PRIMES[h]
    groups = []
    for g in range(primorial(h)):
        blocks = "".join(pair_block(h, g * q + t) for t in range(q))
        if MUTANT and g == 1:
            blocks = blocks[::-1]
        groups.append(cluster + blocks)
    return "".join(groups)


# Lemma 1 on all words of length <= 10 over two letters: fixed by a nontrivial rotation iff proper power.
ok = True
for n in range(1, 11):
    for t in itertools.product("ab", repeat=n):
        w = "".join(t)
        rot = any(w[s:] + w[:s] == w for s in range(1, n))
        ok &= rot == symmetric(w)
check(ok, "Lemma 1: rotation-fixed iff proper power, all binary words of length <= 10")

# Lemma 3 (pairs lemma) on all words over three letters of length <= 12, q = 2, 3, 4.
ok, tested = True, 0
for n in range(2, 13):
    for t in itertools.product("abc", repeat=n):
        w = "".join(t)
        cols = sorted(set(w))
        if len(cols) < 2:
            continue
        for q in (2, 3, 4):
            if n % q:
                continue
            if all(
                keep(w, P) == keep(w, P)[: len(keep(w, P)) // q] * q and len(keep(w, P)) % q == 0
                for P in itertools.combinations(cols, 2)
            ):
                tested += 1
                ok &= w == w[: n // q] * q
check(ok and tested > 0, f"Lemma 3: pair projections q-th powers => word q-th power ({tested} cases, length <= 12)")

# The examples of Section 1 and Figure 1.
check(precarious("AABB"), "AABB is precarious")
check(precarious("ABCCBBCACBBCCB"), "Weiss's k = 3 example ABCCBBCACBBCCB is precarious, length 14")
w4 = "ABCDBACDABDCBACDABCDBADC"
check(precarious(w4) and len(w4) == 24, "Weiss's k = 4 example is precarious, length 24")
check(keep(w4, "AB") == "ABBA" * 3, "Figure 2: the A,B projection is (ABBA)^3")
blocks = [w4[4 * j : 4 * j + 4] for j in range(6)]
check(
    [b[:2] for b in blocks] == ["AB", "BA"] * 3
    and [j for j, b in enumerate(blocks) if b[2:] == "DC"] == [2, 5],
    "Figure 1: A,B alternate every block; C,D reversed exactly in blocks 2 and 5",
)

# Theorem 1 values quoted in the text.
check(
    [a(k) for k in range(2, 11)] == [4, 14, 24, 126, 180, 1290, 1680, 18690, 23100],
    "Theorem 1: a(2..10) = 4, 14, 24, 126, 180, 1290, 1680, 18690, 23100",
)
check(all(closed(k, k - 1) == a(k) for k in range(2, 21)), "Theorem 2 at s = k-1 is Theorem 1 (k <= 20)")
check(
    all(closed(k, 1) == 2 * k and closed(k, 2) == 2 * k + 8 for k in range(3, 21))
    and all(closed(k, 3) == 6 * k for k in range(4, 21)),
    "special cases s = 1, 2, 3 give 2k, 2k+8, 6k",
)

# Table 1, parsed from the .tex.
tex = TEX.read_text()
rows = re.findall(r"^(\d) & ([\d &]+)\\\\", tex, re.M)
table = {int(k): [int(x) for x in vals.split("&") if x.strip()] for k, vals in rows}
check(
    sorted(table) == [3, 4, 5, 6, 7]
    and all(table[k] == [closed(k, s) for s in range(1, k)] for k in table),
    "Table 1 matches formula (2) for 3 <= k <= 7",
)

# Section 3 constructions: s-precarious, k colours, length = formula, all 1 <= s < k <= 7.
ok = True
for k in range(2, 8):
    for s in range(1, k):
        w = construction(k, s)
        good = len(set(w)) == k and len(w) == closed(k, s) and s_precarious(w, s)
        if not good:
            print(f"     construction k={k} s={s} fails")
        ok &= good
check(ok, "Section 3: constructions are s-precarious of length (2) for all 1 <= s < k <= 7")

# The remark: for s = k-1 every nonempty proper deletion is symmetric (k <= 6).
ok = True
for k in range(2, 7):
    w = construction(k, k - 1)
    cols = sorted(set(w))
    for r in range(1, k):
        for D in itertools.combinations(cols, r):
            kept = keep(w, set(cols) - set(D))
            ok &= symmetric(kept)
check(ok, "Remark: every nonempty proper deletion of the s = k-1 constructions is symmetric (k <= 6)")

# Exhaustive minima for the smallest cases (first letter fixed by rotation).
def minimum(k: int, s: int, upto: int) -> int | None:
    al = LETTERS[:k]
    for L in range(k, upto + 1):
        for t in itertools.product(al, repeat=L - 1):
            w = "a" + "".join(t)
            if len(set(w)) == k and s_precarious(w, s):
                return L
    return None


for k, s, want in [(2, 1, 4), (3, 1, 6), (4, 1, 8), (3, 2, 14)]:
    check(minimum(k, s, want) == want, f"exhaustive: shortest {s}-precarious necklace with {k} colours has length {want}")

print("ALL PASS" if not failures else f"FAIL ({len(failures)} checks)")
sys.exit(1 if failures else 0)
