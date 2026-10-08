"""Independent checks of every number and claim printed in the Hofstadter-Conway comparison paper.

Written from the paper's definitions only (it imports none of the research scripts). Checks:
  1. c and s from their recurrences for n <= 2^20: Theorem 1, s slow, s(2^k) = 2^(k-1), the sign pattern;
  2. the operators F, G by their threshold definition agree with the recurrences (2.2), (2.3) on all Dyck words
     of length <= 12, and generate the block words of c and s for every block up to 2^20 (Proposition 4.1);
  3. the worked example (A, B for u = 1100), w_3, v_3, T(w_3) = v_3, and the coordinates of Figure 1;
  4. Lemmas 2.2-2.4 and the key lemma on all symmetric irreducible Dyck words of length <= 34 (26,364 words),
     including the midpoint identity and the contact claim;
  5. Remark 3.2: among all irreducible words, the midpoint identity first fails at length 12 and the bound (3.1) at 16.
Planted mutants at the end must all be KILLED.

Run: nice -n 15 python3 verify_paper.py   (single core, a few minutes)
"""

from __future__ import annotations

import re
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent


def check(name: str, ok: bool) -> None:
    if not ok:
        raise AssertionError(name)
    print("PASS", name, flush=True)


# ---------- words ----------
def prefix(u: list[int]) -> list[int]:
    p = [0]
    for b in u:
        p.append(p[-1] + b)
    return p


def letters(p: list[int]) -> list[int]:
    return [p[i] - p[i - 1] for i in range(1, len(p))]


def is_dyck(u: list[int]) -> bool:
    p = prefix(u)
    return all(2 * p[i] >= i for i in range(len(p))) and 2 * p[-1] == len(u)


def is_irred(u: list[int]) -> bool:
    p = prefix(u)
    return all(2 * p[i] > i for i in range(1, len(u)))


def is_sym(u: list[int]) -> bool:
    n = len(u)
    return all(u[n - 1 - i] == 1 - u[i] for i in range(n))


def le(u: list[int], v: list[int]) -> bool:
    return all(a <= b for a, b in zip(prefix(u), prefix(v)))


def dyck_words(L: int):
    """All Dyck words of length L."""

    def rec(w, ones, zeros):
        if ones == zeros == L // 2:
            yield w
            return
        if ones < L // 2:
            yield from rec(w + [1], ones + 1, zeros)
        if zeros < ones:
            yield from rec(w + [0], ones, zeros + 1)

    yield from rec([], 0, 0)


# ---------- operators ----------
def thresholds_def(u: list[int], mut: str = "") -> tuple[list[int], list[int]]:
    """A(j), B(j) for 0 <= j <= 2L straight from the definition (min / max over I_j)."""
    L = len(u)
    P = prefix(u)
    A, B = [], []
    for j in range(2 * L + 1):
        I = range(max(0, j - L), min(j, L) + 1)
        d = {a: a - P[a] - P[j - a] for a in I}
        if mut == "A_max":
            A.append(max(a for a in I if d[a] >= 0))
        else:
            A.append(min(a for a in I if d[a] >= 0))
        B.append(max(a for a in I if d[a] <= 0))
    return A, B


def thresholds_rec(u: list[int]) -> tuple[list[int], list[int]]:
    """A(j), B(j) by the recurrences (2.2), (2.3), with P(L+1) = P(L)."""
    L = len(u)
    P = prefix(u) + [len(u) // 2]
    A, B = [0], [0]
    for j in range(1, 2 * L + 1):
        a, b = A[-1], B[-1]
        A.append(P[a] + P[j - a])
        B.append(P[b + 1] + P[j - 1 - b])
    return A, B


def F(u):
    return letters(thresholds_rec(u)[0])


def G(u):
    return letters(thresholds_rec(u)[1])


def T(u: list[int], mut: str = "") -> list[int]:
    """The central perturbation: drop the first 1 and last 0, insert b(1-b) at the centre, b = 1 - u_m."""
    m = len(u) // 2
    b = u[m - 1] if mut == "T_b" else 1 - u[m - 1]
    return u[1:m] + [b, 1 - b] + u[m:-1]


# ---------- 1. the sequences ----------
N = 1 << 20
c = [0, 1, 1]
s = [0, 1, 1]
for n in range(3, N + 1):
    c.append(c[c[n - 1]] + c[n - c[n - 1]])
    s.append(n - s[s[n - 1]] - s[n - s[n - 1]])
check(
    "Theorem 1: |s(n) - n/2| <= c(n) - n/2 for n <= 2^20",
    all(abs(2 * s[n] - n) <= 2 * c[n] - n for n in range(1, N + 1)),
)
check(
    "s slow (increments 0 or 1) for n <= 2^20",
    all(s[n] - s[n - 1] in (0, 1) for n in range(2, N + 1)),
)
check(
    "s(2^k) = c(2^k) = 2^(k-1), k <= 20",
    all(s[1 << k] == c[1 << k] == 1 << (k - 1) for k in range(1, 21)),
)
check(
    "sign of s(n) - n/2 is (-1)^k or 0 on [2^k, 2^(k+1)], k <= 19",
    all(
        (-1) ** k * (2 * s[n] - n) >= 0
        for k in range(1, 20)
        for n in range(1 << k, (1 << (k + 1)) + 1)
    ),
)

# ---------- 2. operators and blocks ----------
ok = True
for L in range(2, 13, 2):
    for u in dyck_words(L):
        if thresholds_def(u) != thresholds_rec(u):
            ok = False
check(
    "Lemma 2.2(3): recurrences (2.2), (2.3) agree with the definition, all Dyck words L <= 12",
    ok,
)

w, v = [1, 0], [1, 0]
ok = True
for k in range(1, 20):
    L = 1 << k
    wc = [c[L + t] - c[L + t - 1] for t in range(1, L + 1)]
    vs = [s[L + t] - s[L + t - 1] for t in range(1, L + 1)]
    if k % 2:
        vs = [1 - b for b in vs]
    if wc != w or vs != v:
        ok = False
        break
    w, v = F(w), (F(v) if k % 2 else G(v))
check(
    "Proposition 4.1: w_(k+1) = F(w_k), v_(k+1) = F or G of v_k, every block up to 2^20",
    ok,
)

# ---------- 3. printed examples and Figure 1 ----------
A, B = thresholds_def([1, 1, 0, 0])
check(
    "example: A = 0,1,2,3,3,4,4,4,4 and B = 0,1,2,2,3,3,4,4,4 for u = 1100",
    A == [0, 1, 2, 3, 3, 4, 4, 4, 4] and B == [0, 1, 2, 2, 3, 3, 4, 4, 4],
)
w3, v3 = F([1, 1, 0, 0]), G([1, 1, 0, 0])
check(
    "w_3 = 11101000, v_3 = 11010100, T(w_3) = v_3",
    w3 == [1, 1, 1, 0, 1, 0, 0, 0] and v3 == [1, 1, 0, 1, 0, 1, 0, 0] and T(w3) == v3,
)

tex = (HERE.parent / "paper" / "paper.tex").read_text()
plots = re.findall(r"plot coordinates \{([^}]*)\}", tex)
heights = [[int(y) for _, y in re.findall(r"\((\d+),(\d+)\)", pl)] for pl in plots]
w5 = F(F(w3))
v5 = G(F(v3))


def height(u):
    p = prefix(u)
    return [2 * p[i] - i for i in range(len(p))]


check(
    "Figure 1: the three plotted paths are w_5, T(w_5), v_5",
    len(heights) == 3
    and heights[0] == height(w5)
    and heights[1] == height(T(w5))
    and heights[2] == height(v5),
)
check(
    "Figure 1: w_5 and v_5 are the block words of c and s on [32, 64]",
    w5 == [c[32 + t] - c[31 + t] for t in range(1, 33)]
    and v5 == [1 - (s[32 + t] - s[31 + t]) for t in range(1, 33)],
)


# ---------- 4. the lemmas on symmetric irreducible words ----------
def lemma_checks(u: list[int], mut: str = "") -> bool:
    L = len(u)
    m = L // 2
    Fu, Gu = F(u), G(u)
    if not (is_dyck(Fu) and is_dyck(Gu) and is_irred(Fu) and is_sym(Fu) and is_sym(Gu)):
        return False
    Tu = T(u, mut)
    if not (is_dyck(Tu) and is_sym(Tu) and le(Tu, u)):
        return False
    # (2.6): delta
    P, Pt = prefix(u), prefix(Tu)
    delta = [P[i] - Pt[i] for i in range(L + 1)]
    want = [
        1 - u[i] if i < m else (u[m - 1] if i == m else u[i - 1]) for i in range(L + 1)
    ]
    if delta != want:
        return False
    H = prefix(Fu)
    ww = F(Fu)
    W = prefix(ww)
    Z = prefix(G(F(Tu)))
    M = 2 * L
    if H[M - W[M]] != m:  # midpoint identity
        return False
    for j in range(M + 1):  # contact claim
        if Z[j] == W[j] and ww[j] != 1:
            return False
    return le(G(F(Tu)), T(ww, mut))  # key lemma


ok, count = True, 0
for L in range(4, 35, 2):
    for d in dyck_words(L - 2):
        u = [1] + d + [0]
        if not is_sym(u):
            continue
        count += 1
        if not lemma_checks(u):
            ok = False
check(
    "Lemmas 2.2-2.4 and the key lemma on all symmetric irreducible Dyck words, L <= 34",
    ok,
)
check("there are 26,364 such words", count == 26364)


# ---------- 5. the Remark: without symmetry the midpoint identity and the bound (3.1) fail ----------
def first_failures(L: int) -> tuple[int, int]:
    """For irreducible words of length L: how many violate H(M - W(M)) = m, and how many violate
    H(j - W(j)) <= m for some 0 <= j <= M."""
    m, M = L // 2, 2 * L
    mid = bound = 0
    for d in dyck_words(L - 2):
        u = [1] + d + [0]
        H = prefix(F(u))
        W = prefix(F(F(u)))
        if H[M - W[M]] != m:
            mid += 1
        if max(H[j - W[j]] for j in range(M + 1)) > m:
            bound += 1
    return mid, bound


fails = {L: first_failures(L) for L in range(4, 17, 2)}
check("Remark: midpoint identity holds for all irreducible words of length <= 10, fails for 3 at length 12",
      all(fails[L][0] == 0 for L in range(4, 11, 2)) and fails[12][0] == 3)
check("Remark: bound (3.1) holds for all irreducible words of length <= 14, fails for 8 at length 16",
      all(fails[L][1] == 0 for L in range(4, 15, 2)) and fails[16][1] == 8)


# ---------- mutants ----------
def mutant(name, fn):
    try:
        fn()
    except AssertionError:
        print("MUTANT KILLED", name)
        return
    sys.exit("MUTANT SURVIVED " + name)


mutant(
    "A as the largest instead of the least threshold",
    lambda: check(
        "m", thresholds_def([1, 1, 0, 0], "A_max")[0] == [0, 1, 2, 3, 3, 4, 4, 4, 4]
    ),
)
mutant(
    "T with b = u_m",
    lambda: check(
        "m",
        all(
            lemma_checks(u, "T_b")
            for L in range(4, 13, 2)
            for d in dyck_words(L - 2)
            for u in [[1] + d + [0]]
            if is_sym(u)
        ),
    ),
)
def swapped_blocks_ok() -> bool:
    """Proposition 4.1 with the parities of F and G exchanged for s."""
    v = [1, 0]
    for k in range(1, 8):
        L = 1 << k
        vs = [s[L + t] - s[L + t - 1] for t in range(1, L + 1)]
        if k % 2:
            vs = [1 - b for b in vs]
        if vs != v:
            return False
        v = G(v) if k % 2 else F(v)
    return True


mutant(
    "Theorem 1 with c and s exchanged",
    lambda: check("m", all(abs(2 * c[n] - n) <= 2 * s[n] - n for n in range(1, 2000))),
)
mutant("Proposition 4.1 with F and G exchanged for s", lambda: check("m", swapped_blocks_ok()))
mutant(
    "Figure 1 with the dashed path = w_5", lambda: check("m", heights[1] == height(w5))
)
print("ALL CHECKS PASSED")
