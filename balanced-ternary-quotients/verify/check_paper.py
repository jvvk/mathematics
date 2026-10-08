"""Checks every number and finite claim in the paper (../paper/quotients.tex), from the definitions.

Run: python3 check_paper.py [--quick]     (standard library only)
     --quick skips the 3.7 million carry search for 621*3^16 - 20 (a few seconds and about 1 GB of memory).

The carry sets S_k are rebuilt from carry_sets.json (the data behind Appendix A) by code written
here, independently of the Lean generator. Each check prints PASS; any failure stops the run.
The list of the 200 exceptions below 10^8 is read from exceptions_1e8.txt; search.c recomputes it.
"""

from __future__ import annotations

import json
import re
import sys
from fractions import Fraction
from pathlib import Path

HERE = Path(__file__).resolve().parent
QUICK = "--quick" in sys.argv


def check(name: str, ok: bool) -> None:
    if not ok:
        raise SystemExit(f"FAIL {name}")
    print("PASS", name)


# ---------------------------------------------------------------- balanced ternary and the automaton


def bal(v: int) -> int:
    """The residue of v modulo 3 in {-1, 0, 1}."""
    r = v % 3
    return -1 if r == 2 else r


def digits(x: int) -> list[int]:
    """Balanced ternary digits of x, least significant first."""
    out = []
    while x:
        e = bal(x)
        out.append(e)
        x = (x - e) // 3
    return out


def zero_free(x: int) -> bool:
    return x != 0 and 0 not in digits(x)


def move(n: int, r: int, d: int) -> tuple[int, int] | None:
    """The move (r, d) for multiplication by n: (digit, new carry), or None if dead."""
    v = r + n * d
    e = bal(v)
    return None if e == 0 else (e, (v - e) // 3)


def reachable(n: int) -> tuple[bool, set[int]]:
    """Carries reachable from 0, and whether some reachable move (r, 1) accepts."""
    seen, stack, accept = {0}, [0], False
    while stack:
        r = stack.pop()
        for d in (1, -1):
            m = move(n, r, d)
            if m is None:
                continue
            r2 = m[1]
            if d == 1 and (r2 == 0 or (r2 > 0 and zero_free(r2))):
                accept = True
            if r2 not in seen:
                seen.add(r2)
                stack.append(r2)
    return accept, seen


def member(n: int) -> bool:
    return reachable(n)[0]


def criterion(n: int, S: set[int]) -> bool:
    """Conditions (i) to (iv) of Proposition 2.2 for a finite set S."""
    if 0 not in S or min(S) < 2 - n:
        return False
    for r in S:
        for d in (1, -1):
            m = move(n, r, d)
            if m is None:
                continue
            if m[1] not in S:
                return False
            if d == 1 and m[1] > 0 and zero_free(m[1]):
                return False
    return True


# ---------------------------------------------------------------- Section 1

B = [x for x in range(1, 23) if zero_free(x)]
check(
    "B begins 1,2,4,5,7,11,13,14,16,20,22", B == [1, 2, 4, 5, 7, 11, 13, 14, 16, 20, 22]
)
BMRS = [
    247,
    277,
    967,
    977,
    1211,
    1219,
    1895,
    1937,
    1951,
    1961,
    2183,
    2191,
    2911,
    2921,
    3029,
    3641,
    3649,
]
check(
    "the seventeen exceptions below 3650",
    [n for n in range(2, 3650) if n % 3 and not member(n)] == BMRS,
)

THM1 = [(4, 5, 5), (4, -5, 5), (8, 7, 5), (8, 17, 5), (8, -7, 7)]  # (a, b, first k)
THM2 = [  # (a, b, modulus, residue, first k)
    (8, -17, 2, 0, 6),
    (16, 17, 2, 0, 6),
    (10, -11, 4, 2, 6),
    (10, -19, 4, 2, 6),
    (20, -19, 4, 2, 6),
    (5, -4, 4, 2, 6),
    (5, 4, 4, 0, 8),
    (40, 41, 4, 0, 12),
]
for a, b, k0 in THM1:
    check(
        f"{a}*3^k{b:+d}: not in B/B for k0 <= k <= 22 (decision procedure)",
        all(not member(a * 3**k + b) for k in range(k0, 23)),
    )
    check(
        f"{a}*3^k{b:+d}: sharp, k = {k0 - 1} is in B/B", member(a * 3 ** (k0 - 1) + b)
    )
check(
    "8*3^5 - 7 = 1937 is also an exception", 8 * 3**5 - 7 == 1937 and not member(1937)
)
for a, b, M, res, k0 in THM2:
    ks = [k for k in range(k0, 25) if k % M == res]
    check(
        f"{a}*3^k{b:+d}, k = {res} mod {M}: not in B/B for k0 <= k <= 24",
        all(not member(a * 3**k + b) for k in ks),
    )
    check(
        f"{a}*3^k{b:+d}: sharp, k = {k0 - M} is in B/B", member(a * 3 ** (k0 - M) + b)
    )
check(
    "six of the seventeen lie in the families of Theorem 1",
    sorted(
        n for n in BMRS for a, b, k0 in THM1 for k in range(k0, 9) if a * 3**k + b == n
    )
    == [967, 977, 1951, 1961, 2911, 2921],
)

# ---------------------------------------------------------------- Section 2

check("n = 5: move (0,1) gives digit -1 and carry 2", move(5, 0, 1) == (-1, 2))
check("5 = (1 -1 -1) in balanced ternary", digits(5) == [-1, -1, 1])


# ---------------------------------------------------------------- Section 3: n = 4*3^k + 5


def S_first(k: int) -> set[int]:
    X = 3**k
    c = 2 * X + 2
    pos = {c} | {c - 2 * 3**i for i in range(k)} | {c - 4 * 3**i for i in range(k)}
    return {0} | pos | {-x for x in pos}


for k in range(5, 41):
    X, n = 3**k, 4 * 3**k + 5
    c = 2 * X + 2
    S = S_first(k)
    assert len(S) == 4 * k + 3, k
    rows = [  # Table 1: (carry, digit, expected result) with i = 1..k-1 for the chain rows
        (0, 1, (-1, c - 2 * 3 ** (k - 1))),
        (0, -1, (1, -(c - 2 * 3 ** (k - 1)))),
        (c, 1, (1, c)),
        (c, -1, None),
        (c - 2, 1, (-1, c)),
        (c - 2, -1, (1, -(c - 4 * 3 ** (k - 1)))),
        (c - 4, 1, None),
        (c - 4, -1, (-1, -(c - 4 * 3 ** (k - 1)))),
    ]
    for i in range(1, k):
        rows += [
            (c - 2 * 3**i, 1, (1, c - 2 * 3 ** (i - 1))),
            (c - 2 * 3**i, -1, None),
            (c - 4 * 3**i, 1, (1, c - 4 * 3 ** (i - 1))),
            (c - 4 * 3**i, -1, None),
        ]
    assert all(move(n, r, d) == res for r, d, res in rows), k
    assert {r for r, _, _ in rows} == {r for r in S if r >= 0}, k
    assert criterion(n, S) and max(abs(r) for r in S) == c < n - 2, k
    # the explicit expansions in "No accepting move"
    assert c == 3 ** (k + 1) - 3**k + 3 - 1 and digits(c)[2] == 0
    for j in range(2, k - 1):
        for x in (c - 2 * 3**j, c - 4 * 3**j):
            assert sorted(p for p, e in enumerate(digits(x)) if e) == sorted(
                {0, 1, j, j + 1, k, k + 1}
            ), (k, j)
            assert 0 in digits(x)
    assert (
        digits(c - 2)[0] == 0
        and digits(c - 4)[2] == 0
        and digits(c - 6)[2] == 0
        and digits(c - 12)[1] == 0
    )
    assert digits(c - 2 * 3 ** (k - 1))[2] == 0 and digits(c - 4 * 3 ** (k - 1))[2] == 0
check(
    "Section 3: Table 1, |S_k| = 4k+3, conditions (i)-(iv), the digit expansions, 5 <= k <= 40",
    True,
)
check(
    "329 = 4*3^4+5 in B/B: 329*4 = 1316 = (1 -1 -1 1 1 -1 1 -1)",
    4 * 81 + 5 == 329
    and 329 * 4 == 1316
    and digits(4) == [1, 1]
    and digits(1316)[::-1] == [1, -1, -1, 1, 1, -1, 1, -1],
)

# ---------------------------------------------------------------- Section 4 and Appendix A


def S_from_json(groups: list[dict], k: int) -> set[int]:
    """Expand a carry set of Appendix A: sporadic gX + s, chains gX + beta - t*3^i."""
    X, S = 3**k, {0}
    for grp in groups:
        g, beta = Fraction(*grp["g"]), Fraction(*grp["beta"])
        for s in grp["spor"]:
            v = g * X + Fraction(*s)
            assert v.denominator == 1
            S.add(grp["sg"] * int(v))
        for ch in grp["chains"]:
            for i in range(ch["lo"], k - ch["hi"] + 1):
                if (i - ch["res"]) % ch["st"] == 0:
                    v = g * X + beta - ch["t"] * 3**i
                    assert v.denominator == 1
                    S.add(grp["sg"] * int(v))
    return S


SETS = json.load(open(HERE / "carry_sets.json"))
for a, b, _ in THM1:
    for k in range(14, 41):
        S = S_from_json(SETS[f"{a},{b},{k % 2}"], k)
        assert S == {-x for x in S} and criterion(a * 3**k + b, S), (a, b, k)
    for k in range(10, 25):
        assert reachable(a * 3**k + b)[1] == S_from_json(SETS[f"{a},{b},{k % 2}"], k), (
            a,
            b,
            k,
        )
    check(
        f"{a}*3^k{b:+d}: Appendix A set satisfies (i)-(iv) for 14 <= k <= 40, equals the reachable set for 10 <= k <= 24",
        True,
    )
for a, b, M, res, _ in THM2:
    for k in range(14, 41):
        if k % M == res:
            S = S_from_json(SETS[f"{a},{b},{M},{res}"], k)
            assert S == {-x for x in S} and criterion(a * 3**k + b, S), (a, b, k)
    check(
        f"{a}*3^k{b:+d}, k = {res} mod {M}: Appendix A set satisfies (i)-(iv) for 14 <= k <= 40",
        True,
    )
check(
    "4*3^k-5 example in Section 4 matches Appendix A (k = 14..20)",
    all(
        S_from_json(SETS[f"4,-5,{k % 2}"], k)
        == {0}
        | {
            s * x
            for s in (1, -1)
            for x in (
                {2 * 3**k // 3, 2 * 3**k // 3 + 2}
                | {2 * 3**k - 2 - 2 * 3**i for i in range(k)}
                | {2 * 3**k - 2 - t * 3**i for t in (4, 8) for i in range(k - 1)}
            )
        }
        for k in range(14, 21)
    ),
)

for n, m, N in ((4 * 81 - 5, 4, 1276), (8 * 81 + 7, 2, 1310), (8 * 81 + 17, 2, 1330)):
    check(
        f"witness {n}*{m} = {N}, both zero-free",
        n * m == N and zero_free(m) and zero_free(N),
    )
check("digits: 4 = (11), 2 = (1 -1)", digits(4) == [1, 1] and digits(2) == [-1, 1])
W = 8620770364
check(
    "8*3^6-7 = 5825: 5825*8620770364 = 50215987370300, both zero-free",
    8 * 729 - 7 == 5825
    and 5825 * W == 50215987370300
    and zero_free(W)
    and zero_free(5825 * W),
)


def zero_free_upto(limit: int) -> list[int]:
    """All positive zero-free integers below limit (leading digit +1)."""
    out, level = [], [1]
    while level:
        out += [x for x in level if x < limit]
        level = [3 * x + e for x in level for e in (1, -1) if 3 * x - 1 < limit]
    return out


check(
    "8620770364 is the smallest witness for 5825",
    min(m for m in zero_free_upto(W + 1) if zero_free(5825 * m)) == W,
)

# ---------------------------------------------------------------- Section 6: exceptions below 10^8

EX = [
    int(line.split()[0])
    for line in open(HERE / "exceptions_1e8.txt")
    if line.strip() and line[0].isdigit()
]
check(
    "200 exceptions below 10^8, the first seventeen as in BMRS",
    len(EX) == 200
    and EX[:17] == BMRS
    and all(n % 3 and n < 10**8 for n in EX)
    and EX == sorted(set(EX)),
)
check("each listed exception is outside B/B", all(not member(n) for n in EX))


def in_family(n: int, a: int, b: int, k0: int, M: int = 1, res: int = 0) -> bool:
    k = k0
    while a * 3**k + b <= n:
        if a * 3**k + b == n and k % M == res:
            return True
        k += 1
    return False


t1 = [n for n in EX if any(in_family(n, a, b, k0) for a, b, k0 in THM1)]
t2 = [n for n in EX if any(in_family(n, a, b, k0, M, r) for a, b, M, r, k0 in THM2)]
check("50 exceptions below 10^8 lie in the families of Theorem 1", len(t1) == 50)
check(
    "75 lie in the families of Theorems 1 and 2 together", len(set(t1) | set(t2)) == 75
)
check(
    "first five families of Theorem 2: every exception below 10^8 of that form is in the stated class",
    all(
        not in_family(n, a, b, 1) or in_family(n, a, b, k0, M, r)
        for n in EX
        for a, b, M, r, k0 in THM2[:5]
    ),
)

# families a*3^k + b with at least three members (as in Table 2)
fam: dict[tuple[int, int], set[int]] = {}
for n in EX:
    k = 1
    while 3**k <= 2 * n:
        q, rem = divmod(n, 3**k)
        for aa, bb in ((q, rem), (q + 1, rem - 3**k)):
            if 0 < aa <= 300 and aa % 3 and abs(bb) <= 300 and 3**k > 3 * abs(bb):
                fam.setdefault((aa, bb), set()).add(n)
        k += 1
fams = {f: s for f, s in fam.items() if len(s) >= 3}
inside = set().union(*fams.values())
check(
    "136 exceptions fall into 21 families with at least three members; 64 into none",
    len(fams) == 21 and len(inside) == 136 and len(EX) - len(inside) == 64,
)


def pattern(a: int, b: int) -> str:
    out, k = "", 1
    while a * 3**k + b <= 10**8:
        n = a * 3**k + b
        out += ("x" if n in EX else ".") if n > 0 and n % 3 else "~"
        k += 1
    return out


TEX = [HERE.parent / "paper" / "quotients.tex", HERE.parent.parent / "quotients.tex"]  # repository, arXiv anc/
tex = next(t for t in TEX if t.exists()).read_text()
rows = re.findall(
    r"^\$(\d+)\\cdot 3\^k([+-]) ?(\d+)\$ & \\texttt\{([^}]*)\}|^\$3\^k([+-])(\d+)\$ & \\texttt\{([^}]*)\}",
    tex,
    re.MULTILINE,
)
table = {}
for a, s, b, p, s2, b2, p2 in rows:
    if a:
        table[(int(a), int(b) * (1 if s == "+" else -1))] = p
    else:
        table[(1, int(b2) * (1 if s2 == "+" else -1))] = p2
check("Table 2 lists exactly the 21 families", set(table) == set(fams))
check(
    "Table 2 patterns match the data",
    all(pattern(a, b).rstrip() == p.rstrip() for (a, b), p in table.items()),
)

# ---------------------------------------------------------------- Section 6: digits 0 and 1

check(
    "621*3^(4k)-20 for k = 1, 2, 3, 4",
    [621 * 3 ** (4 * k) - 20 for k in (1, 2, 3, 4)]
    == [50281, 4074361, 330024841, 26732013721],
)


def in_C(x: int) -> bool:
    while x:
        if x % 3 == 2:
            return False
        x //= 3
    return True


def reach01(n: int) -> tuple[bool, int]:
    """Digits {0,1}: carries reachable from 0 when multiplying by n, and whether one accepts."""
    seen, stack = {0}, [0]
    while stack:
        r = stack.pop()
        for d in (0, 1):
            v = r + n * d
            if v % 3 == 2:
                continue
            r2 = (v - v % 3) // 3
            if d == 1 and in_C(r2):
                return True, len(seen)
            if r2 not in seen:
                seen.add(r2)
                stack.append(r2)
    return False, len(seen)


def in_D(N: int) -> bool:
    i = 1
    while 3 ** (i - 1) <= N:
        if N % 3**i == 2 * 3 ** (i - 1):
            return True
        i += 1
    return False


def in_E(N: int) -> bool:
    return any(3 * 3**i <= 2 * N <= 4 * 3**i for i in range(40))


counts = [870, 14368, 230658, 3691740]
for k in (1, 2, 3) if QUICK else (1, 2, 3, 4):
    N = 621 * 3 ** (4 * k) - 20
    acc, cnt = reach01(N)
    check(
        f"621*3^{4 * k}-20 = {N}: in F ({cnt} reachable carries)",
        not acc and cnt == counts[k - 1] and N % 3 == 1 and not in_D(N) and not in_E(N),
    )

# ---------------------------------------------------------------- mutants: each must be caught
k = 9
S = S_first(k)
mutants = {
    "S_k for 4*3^k+5 missing one carry": not criterion(4 * 3**k + 5, S - {2 * 3**k + 2 - 4 * 3**3}),
    "S_k used for 4*3^k+7": not criterion(4 * 3**k + 7, S),
    "8*3^k+17 set used for 8*3^k+19": not criterion(8 * 3**14 + 19, S_from_json(SETS["8,17,0"], 14)),
    "5*3^k+4 class set used for k = 1 mod 4": not criterion(5 * 3**17 + 4, S_from_json(SETS["5,4,4,0"], 17)),
    "a member (k = 4) passed as an exception": member(4 * 81 + 5),
    "Table 2 pattern with one symbol changed": pattern(4, 5).replace("x", ".", 1) != pattern(4, 5),
}
for name, caught in mutants.items():
    check(f"mutant caught: {name}", caught)
print("ALL CHECKS PASSED" + (" (quick: k = 4 of the 621 family skipped)" if QUICK else ""))
