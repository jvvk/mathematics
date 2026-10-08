"""Exact checks of every number quoted in paper/mex.tex, and of each proof step on the computed terms.

Run: python3 verify_paper.py   (standard library only; a few seconds)
Mutants at the end must all be KILLED.
"""

from __future__ import annotations


def mex(s: set[int]) -> int:
    v = 0
    while v in s:
        v += 1
    return v


def mex_seq(start: list[int], n_terms: int) -> list[int]:
    a = list(start)
    while len(a) < n_terms:
        n = len(a) - 1
        a.append(mex({a[i] + a[n - i] for i in range(n + 1)}))
    return a


def y(b: int) -> int:
    return [1, 1, 3][b] if b < 3 else [2, 5, 4][(b - 3) % 3] + 4 * ((b - 3) // 3)


def w(b: int) -> int:
    return [1, 3, 3][b] if b < 3 else 2


def closed(n: int) -> int:
    if n == 0:
        return 1
    b, j = divmod(n, 5)
    return 0 if j in (0, 3) else y(b) if j in (1, 2) else w(b)


def check(name: str, ok: bool) -> None:
    if not ok:
        raise AssertionError(name)
    print("PASS", name)


# mex examples
check("mex{0,1,3}=2", mex({0, 1, 3}) == 2)
check("mex{1,2}=0", mex({1, 2}) == 0)

# Guy's example 1,4,3,2 (OEIS A067017): printed continuation and period 14 from index 3
g = mex_seq([1, 4, 3, 2], 400)
check(
    "Guy continuation",
    g[4:22] == [0, 0, 0, 0, 0, 5, 1, 1, 1, 1, 1, 6, 2, 2, 0, 0, 0, 0],
)
check("Guy period 14 from a_3", all(g[i] == g[i + 14] for i in range(3, 330)))
check(
    "Guy not periodic from a_2",
    any(g[i] != g[i + 14] for i in range(2, 380)) and g[2] != g[16],
)
per = min(p for p in range(1, 60) if all(g[i] == g[i + p] for i in range(3, 330)))
check("Guy least period is 14", per == 14)

# Max sequence (A067016) 1,4,3,2 -> 7,8,11,12,15,16 with differences as printed by Guy
mx = [1, 4, 3, 2]
while len(mx) < 12:
    n = len(mx) - 1
    mx.append(max(mx[i] + mx[n - i] for i in range(n + 1)))
check("max sequence 7,8,11,12,15,16", mx[4:10] == [7, 8, 11, 12, 15, 16])

# Our sequence
A = mex_seq([1, 1, 1, 0, 1, 0, 1, 1], 3000)
check("a_8 = mex{1,2} = 0", {A[i] + A[7 - i] for i in range(8)} == {1, 2} and A[8] == 0)
table = [A[5 * b : 5 * b + 5] for b in range(12)]
check(
    "first sixty terms table",
    table
    == [
        [1, 1, 1, 0, 1],
        [0, 1, 1, 0, 3],
        [0, 3, 3, 0, 3],
        [0, 2, 2, 0, 2],
        [0, 5, 5, 0, 2],
        [0, 4, 4, 0, 2],
        [0, 6, 6, 0, 2],
        [0, 9, 9, 0, 2],
        [0, 8, 8, 0, 2],
        [0, 10, 10, 0, 2],
        [0, 13, 13, 0, 2],
        [0, 12, 12, 0, 2],
    ],
)
check("closed form, 3000 terms", all(A[n] == closed(n) for n in range(3000)))
check("max of first 3000 terms is 797", max(A) == 797)
check("y grows by 4 every 3 blocks", all(y(b + 3) == y(b) + 4 for b in range(3, 500)))
check("y_b distinct for b>=1", len({y(b) for b in range(1, 500)}) == 499)

# Worked step: m = 41 = 5*8+1, b = 8
b = 8
S41 = {A[i] + A[40 - i] for i in range(41)}
T8 = {0, 1} | {y(c) for c in range(b)} | {y(c) + w(b - 1 - c) for c in range(b)}
check("S_41 = T_8", S41 == T8)
print("   T_8 =", sorted(T8), " y_0..y_7 =", [y(c) for c in range(8)])
check("mex T_8 = 8 = y_8 = a_41 = a_42", mex(T8) == 8 == y(8) == A[41] == A[42])
copied = {y(c) for c in range(b)}
check("copied values y_0..y_7 = {1,3,2,5,4,6,9}", copied == {1, 2, 3, 4, 5, 6, 9})
S42 = {A[i] + A[41 - i] for i in range(42)}
check(
    "S_42 = T_8 with 0 and 1+y_8",
    S42 == ({0, 1 + y(8)} | copied | {y(c) + w(b - 1 - c) for c in range(b)}),
)
# m = 44 = 5*8+4: a_44 = 2
S44 = {A[i] + A[43 - i] for i in range(44)}
check(
    "a_44: 0,1 in S, 2 not in S", 0 in S44 and 1 in S44 and 2 not in S44 and A[44] == 2
)

# Copying mechanism at m=41 (n=40): pairs (i, 40-i) with a zero at 40-i give a_i
zero_pairs = sorted({A[i] for i in range(41) if A[40 - i] == 0})
check("zeros copy y_0..y_7 (and 0, 1)", set(zero_pairs) == {0, 1} | copied)

# Second example
B = mex_seq([1, 1, 0, 0, 1, 1, 0, 1, 0, 1, 1, 1], 4000)
check(
    "second example: a_{n+48} = a_n or a_n + 7 from n=74",
    all(B[n + 48] - B[n] in (0, 7) for n in range(74, 3900)),
)
grow = [r for r in range(48) if B[74 + r + 48] - B[74 + r] == 7]
check(
    "second example: 18 growing residues",
    len(grow) == 18
    and all(
        B[n + 48] - B[n] == (7 if (n - 74) % 48 in grow else 0) for n in range(74, 3900)
    ),
)
# r = 2 extras: b = 3k+5 -> y_{b-3}+3, y_{b-2}+3, y_{b-1}+1 = 4k+3, 4k+5, 4k+6
check(
    "r=2 extra elements",
    all(
        (y(3 * k + 2) + 3, y(3 * k + 3) + 3, y(3 * k + 4) + 1)
        == (4 * k + 3, 4 * k + 5, 4 * k + 6)
        for k in range(1, 200)
    ),
)
check(
    "r=0 extra elements",
    all(
        (y(3 * k) + 3, y(3 * k + 1) + 3, y(3 * k + 2) + 1)
        == (4 * k + 1, 4 * k + 4, 4 * k + 1)
        for k in range(1, 200)
    ),
)
check(
    "r=1 extra elements",
    all(
        (y(3 * k + 1) + 3, y(3 * k + 2) + 3, y(3 * k + 3) + 1)
        == (4 * k + 4, 4 * k + 3, 4 * k + 3)
        for k in range(1, 200)
    ),
)

# Zero set: Y = Z+1 satisfies y in Y iff y not in Y+Y (for y >= k+2), checked on our example
k = 7
Z = {n for n in range(3000) if A[n] == 0}
Y = {z + 1 for z in Z}
check(
    "Y greedy beyond start",
    all(
        ((yv in Y) == (not any((yv - u) in Y for u in Y if u < yv)))
        for yv in range(k + 2, 2900)
    ),
)
# Calkin-Finch base {1,3,8,20,26}: mex sequence with zeros at base-1 has zero set = completion - 1
base = {1, 3, 8, 20, 26}
start = [0 if i + 1 in base else 1 for i in range(26)]
C = mex_seq(start, 1500)
comp = set(base)
for v in range(27, 1500):
    if not any((v - u) in comp for u in comp if u < v):
        comp.add(v)
check(
    "zero set of CF-base mex sequence = sum-free completion shifted",
    {n + 1 for n in range(1499) if C[n] == 0} == {v for v in comp if v <= 1499},
)


# Mutants
def mutant(name, fn):
    try:
        fn()
    except AssertionError:
        print("MUTANT KILLED", name)
        return
    raise SystemExit("MUTANT SURVIVED " + name)


mutant("slope 3", lambda: check("m", all(y(b + 3) == y(b) + 3 for b in range(3, 50))))
mutant("y_8 = 9", lambda: check("m", mex(T8) == 9))
mutant("Guy period 7", lambda: check("m", all(g[i] == g[i + 7] for i in range(3, 380))))
mutant("w_b = 3", lambda: check("m", all(A[5 * b + 4] == 3 for b in range(3, 100))))
mutant(
    "start 0 not 1",
    lambda: check(
        "m",
        mex_seq([0, 1, 1, 0, 1, 0, 1, 1], 600)[1:]
        == [closed(n) for n in range(1, 600)],
    ),
)
print("ALL CHECKS PASSED")

# Numerical examples in the text.
for b, expected in (
    (9, set(range(10)) | {12}),
    (10, set(range(13))),
    (11, set(range(12)) | {13, 14}),
):
    actual = {A[i] + A[5 * b - i] for i in range(5 * b + 1)}
    check(f"first-gap illustration T_{b}", actual == expected)
check("new first gaps 10,13,12", [A[5 * b + 1] for b in (9, 10, 11)] == [10, 13, 12])
check(
    "second example: every available comparison through n=3951",
    all(
        B[n + 48] - B[n] == (7 if (n - 74) % 48 in grow else 0) for n in range(74, 3952)
    ),
)
check(
    "periodic increments from n=15",
    all(A[n + 15] - A[n] == (4 if n % 5 in (1, 2) else 0) for n in range(15, 2985)),
)
D = mex_seq([0, 1, 0], 200)
check(
    "sum-free example has shifted odd zero positions",
    {n + 1 for n in range(200) if D[n] == 0} == set(range(1, 201, 2)),
)
check("zero-shift example: a_3=a_5=0 but a_9!=0", A[3] == A[5] == 0 and A[9] != 0)
print("ALL TEXT EXAMPLE CHECKS PASSED")

# Checks of the proof in Section 4 (Lemmas 1 and 2), using the recurrence rather than the closed form.
check("zero pattern at all 2999 positive positions", all(
    (A[m] == 0) == (m % 5 in (0, 3)) for m in range(1, len(A))
))
for m in range(8, len(A)):
    if m % 5 in (1, 2, 4):
        i, j = (5, m - 6) if m % 5 == 1 else (3, m - 4)
        assert 0 < i < m and 0 < j < m and i + j == m - 1
        assert A[i] == A[j] == 0
check("zero-pair witnesses for every positive generated position", True)
for b in range(2, 200):
    first = 5 * b + 1
    first_set = {A[i] + A[first - 1 - i] for i in range(first)}
    second_set = {A[i] + A[first - i] for i in range(first + 1)}
    assert second_set == first_set | {1 + A[first]}
    assert all(A[5 * c + 1] in first_set for c in range(b))
    assert A[first] == A[first + 1] and A[first] >= 2
check("twins: same copied values and only the extra boundary sum", True)
check("last-column induction conclusion for all available blocks", all(
    A[5 * b + 4] == 2 for b in range(3, len(A) // 5)
))
print("ALL SECTION 4 PROOF CHECKS PASSED")

# Sentences of Sections 3 and 5.
check("set for a_41 is {0,...,7,9,10}", S41 == {0, 1, 2, 3, 4, 5, 6, 7, 9, 10})
check(
    "from n=15, 15 positions ahead adds 4 at twin positions and 0 elsewhere",
    all(A[n + 15] - A[n] == (4 if n % 5 in (1, 2) else 0) for n in range(15, len(A) - 15)),
)
check("not from n=14", A[14 + 15] - A[14] != 0)
print("ALL SECTION 3 AND 5 CHECKS PASSED")
