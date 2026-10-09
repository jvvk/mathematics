"""Independent recheck for MO 453809 (Lev's matrix zero-forcing game). Shares no code with Codex's scripts.

From the rules only (row i: the Enemy selects i positions, You pick one selected position per row, You win if
the picked entries sum to 0):

1. n = 3: the literal game agrees with the criterion "for every a in A, at least two positions of B have
   -a-b in C", on every matrix with sorted rows from {-3..3}.
2. n = 3, all rows with distinct entries: winning iff, after the normalisation (A+u+v, B-u, C-v) with
   u = min B, v = min C, the rows form one of the five families I-V (own implementation).
3. n = 3: the maximal winning linear subspaces. Enumerate the minimal hitting patterns (two B-positions per
   A-position, one C-partner each), take exact rational row spaces, keep the inclusion-minimal ones; count
   the complements by dimension (expected 99 of dim 5, 576 of dim 4, 432 of dim 3: 1,107 in all), and check
   the maximum is n(n+1)/2 - 1 = 5.
4. The two-valued normal form: random matrices with at most two values per row, n <= 5, literal game versus
   the quantified sum formula (universal / fixed / existential rows).
5. The subset-sum embedding: random instances "for all x exists y: sum u_j^{x_j} + sum v_j^{y_j} = T",
   literal game on the constructed 2m x 2m matrix versus brute-force truth.
6. The families at every order: paired rows (even n), Hall's family, the repeated-value family; random
   instances are winning by the literal game, n = 4..6; and their parameter counts.
7. Mutants: a wrong criterion (one usable position instead of two), a wrong family, a wrong embedding
   (existential rows in the upper half) are rejected.

Run: python recheck.py [--quick]
"""

from __future__ import annotations

import itertools
import random
import sys
from fractions import Fraction as Fr

QUICK = "--quick" in sys.argv
rng = random.Random(453809)
FAIL: list[str] = []


def check(name: str, ok: bool, detail: str = "") -> None:
    print(f"{'PASS' if ok else 'FAIL'}  {name}  {detail}", flush=True)
    if not ok:
        FAIL.append(name)


# ------------------------------------------------------------------ the literal game
def wins(M: list[list]) -> bool:
    """Row i (1-based) of M: the Enemy picks i positions; You need a zero-sum transversal of the picks."""
    n = len(M)
    picks = [list(itertools.combinations(range(len(M[i])), i + 1)) for i in range(n)]

    def reachable(i: int, sel: tuple) -> set:
        # sums available from rows i.. given the Enemy's selections sel[i:]
        if i == n:
            return {0}
        rest = reachable(i + 1, sel)
        return {M[i][j] + s for j in sel[i] for s in rest}

    for sel in itertools.product(*picks):
        if 0 not in reachable(0, sel):
            return False
    return True


# ------------------------------------------------------------------ 1. the 3x3 criterion
def criterion3(A, B, C) -> bool:
    Cs = set(C)
    return all(sum(1 for b in B if -a - b in Cs) >= 2 for a in A)


def criterion3_mutant(A, B, C) -> bool:
    Cs = set(C)
    return all(sum(1 for b in B if -a - b in Cs) >= 1 for a in A)


vals = range(-3, 4)
rows = list(itertools.combinations_with_replacement(vals, 3))
if QUICK:
    rows = rows[::3]
agree = total = mutant_caught = 0
for A in rows:
    for B in rows:
        for C in rows:
            w = wins([list(A), list(B), list(C)])
            total += 1
            agree += w == criterion3(A, B, C)
            mutant_caught += w != criterion3_mutant(A, B, C)
check(
    "3x3: literal game = criterion (two usable positions)",
    agree == total,
    f"{agree}/{total}",
)
check(
    "  mutant (one usable position) disagrees somewhere",
    mutant_caught > 0,
    f"{mutant_caught} cases",
)


# ------------------------------------------------------------------ 2. five families (distinct entries)
def five_families(A, B, C) -> bool:
    u, v = min(B), min(C)
    a = sorted(x + u + v for x in A)
    b = sorted(x - u for x in B)
    c = sorted(x - v for x in C)
    p, q = b[1], b[2] - b[1]
    fams = []
    fams.append((sorted([-p, -p - q, -2 * p - q]), b, b))  # I
    h = b[1]
    fams.append((sorted([-h, -2 * h, -3 * h]), [0, h, 2 * h], [0, h, 3 * h]))  # II
    fams.append(
        (sorted([-2 * h, -3 * h, -4 * h]), [0, h, 2 * h], [0, 2 * h, 3 * h])
    )  # III
    fams.append((sorted([-h, -2 * h, -3 * h]), [0, h, 3 * h], [0, h, 2 * h]))  # IV
    h2 = b[2] - b[1]  # family V has b = (0, 2h, 3h), so the top gap is h
    fams.append(
        (sorted([-2 * h2, -3 * h2, -4 * h2]), [0, 2 * h2, 3 * h2], [0, h2, 2 * h2])
    )  # V
    return any(a == fa and b == fb and c == fc for fa, fb, fc in fams)


distinct_rows = [r for r in itertools.combinations(range(-4, 5), 3)]
if QUICK:
    distinct_rows = distinct_rows[::2]
agree = total = nwin = 0
for A in distinct_rows:
    for B in distinct_rows:
        for C in distinct_rows:
            w = criterion3(
                A, B, C
            )  # = literal game by check 1, and checked again on the winners below
            total += 1
            nwin += w
            agree += w == five_families(A, B, C)
check(
    "3x3 distinct entries: winning iff one of the five families",
    agree == total,
    f"{agree}/{total}, {nwin} winning",
)
sample = [
    (A, B, C)
    for A in distinct_rows[::7]
    for B in distinct_rows[::5]
    for C in distinct_rows
    if five_families(A, B, C)
]
check(
    "  every family member found is winning in the literal game",
    all(wins([list(A), list(B), list(C)]) for A, B, C in sample),
    f"{len(sample)} members",
)


def five_families_mutant(A, B, C) -> bool:  # family II with A = (-h, -2h, -4h)
    u, v = min(B), min(C)
    a = sorted(x + u + v for x in A)
    b = sorted(x - u for x in B)
    c = sorted(x - v for x in C)
    h = b[1]
    return (
        a == sorted([-h, -2 * h, -4 * h]) and b == [0, h, 2 * h] and c == [0, h, 3 * h]
    )


bad = [
    (A, B, C)
    for A in distinct_rows
    for B in distinct_rows[:40]
    for C in distinct_rows
    if five_families_mutant(A, B, C)
]
check(
    "  mutant family (II with A = -h,-2h,-4h) is losing",
    bool(bad) and not any(wins([list(A), list(B), list(C)]) for A, B, C in bad[:20]),
    f"{len(bad)} instances",
)


# ------------------------------------------------------------------ 3. maximal winning subspaces, n = 3
def rref(vectors: list[list[Fr]]) -> tuple:
    rows_ = [list(v) for v in vectors]
    col = 0
    ncol = len(rows_[0]) if rows_ else 0
    r = 0
    while r < len(rows_) and col < ncol:
        pr = next((i for i in range(r, len(rows_)) if rows_[i][col] != 0), None)
        if pr is None:
            col += 1
            continue
        rows_[r], rows_[pr] = rows_[pr], rows_[r]
        pv = rows_[r][col]
        rows_[r] = [x / pv for x in rows_[r]]
        for i in range(len(rows_)):
            if i != r and rows_[i][col] != 0:
                f = rows_[i][col]
                rows_[i] = [x - f * y for x, y in zip(rows_[i], rows_[r])]
        r += 1
        col += 1
    return tuple(tuple(x) for x in rows_[:r])


def inc(t: tuple) -> list[Fr]:
    v = [Fr(0)] * 9
    for i, j in enumerate(t):
        v[3 * i + j] = Fr(1)
    return v


def contains(big: tuple, small: tuple) -> bool:
    return len(rref(list(big) + list(small))) == len(big)


spaces = set()
pair_choices = list(itertools.combinations(range(3), 2))
per_a = []
for i in range(3):
    opts = []
    for pair in pair_choices:
        for c1 in range(3):
            for c2 in range(3):
                opts.append(((i, pair[0], c1), (i, pair[1], c2)))
    per_a.append(opts)
for combo in itertools.product(*per_a):
    ts = [t for two in combo for t in two]
    spaces.add(rref([inc(t) for t in ts]))
spaces = sorted(spaces, key=len)
minimal = []
for s in spaces:
    if not any(len(m) < len(s) and contains(s, m) for m in minimal):
        minimal.append(s)
by_dim: dict[int, int] = {}
for m in minimal:
    by_dim[9 - len(m)] = by_dim.get(9 - len(m), 0) + 1
check(
    "3x3: maximal winning subspaces 99 (dim 5) + 576 (dim 4) + 432 (dim 3) = 1107",
    by_dim == {5: 99, 4: 576, 3: 432},
    f"{dict(sorted(by_dim.items()))}, {len(spaces)} spans",
)
check("  maximum dimension = n(n+1)/2 - 1 = 5", max(by_dim) == 5)

# a random point of a random component is winning; a perturbation off every component is not
ok = True
for m in rng.sample(minimal, 40 if QUICK else 150):
    # complement basis: solve m . x = 0
    piv = [next(k for k, x in enumerate(r) if x != 0) for r in m]
    free = [k for k in range(9) if k not in piv]
    x = [Fr(0)] * 9
    for k in free:
        x[k] = Fr(rng.randint(-5, 5))
    for r, pk in zip(m, piv):
        x[pk] = -sum(r[k] * x[k] for k in free)
    M = [x[0:3], x[3:6], x[6:9]]
    ok &= wins(M)
check("  random points of the components are winning (literal game)", ok)

# orbits under independent permutations of positions within each row
perms = list(itertools.permutations(range(3)))


def permute(space: tuple, pr: tuple) -> tuple:
    # pr = (perm of row 0, row 1, row 2); coordinate 3*i + j goes to 3*i + pr[i][j]
    rows_ = []
    for r in space:
        v = [Fr(0)] * 9
        for i in range(3):
            for j in range(3):
                v[3 * i + pr[i][j]] = r[3 * i + j]
        rows_.append(v)
    return rref(rows_)


comp_set = set(minimal)
seen: set = set()
orbits = 0
for m in minimal:
    if m in seen:
        continue
    orbits += 1
    for pr in itertools.product(perms, repeat=3):
        seen.add(permute(m, pr))
check("  the 1107 components form 12 orbits under permutations within rows",
      orbits == 12 and seen == comp_set, f"{orbits} orbits")


# distinct entries: an equality x_ij = x_ik holds on the component iff e_ij - e_ik lies in its row space
def forces_equal_in_some_row(space: tuple) -> bool:
    for i in range(3):
        for j, k in ((0, 1), (0, 2), (1, 2)):
            e = [Fr(0)] * 9
            e[3 * i + j], e[3 * i + k] = Fr(1), Fr(-1)
            if contains(space, (tuple(e),)):
                return True
    return False


d5 = [m for m in minimal if 9 - len(m) == 5]
d4_distinct = [m for m in minimal if 9 - len(m) == 4 and not forces_equal_in_some_row(m)]
check("  every 5-dimensional component forces two equal entries in some row",
      all(forces_equal_in_some_row(m) for m in d5), f"{len(d5)} components")
check("  some 4-dimensional component has generically distinct rows", len(d4_distinct) > 0,
      f"{len(d4_distinct)} components")


# ------------------------------------------------------------------ 4. two-valued normal form
def two_valued_formula(M) -> bool:
    n = len(M)
    fixed, univ, exist = 0, [], []
    for i, row in enumerate(M, start=1):
        vs = sorted(set(row))
        if len(vs) == 1:
            fixed += vs[0]
            continue
        u, v = vs
        al, be = row.count(u), row.count(v)
        if al >= i and be >= i:
            univ.append((u, v))
        elif al >= i:
            fixed += u
        elif be >= i:
            fixed += v
        else:
            exist.append((u, v))
    for xs in itertools.product(*univ):
        base = fixed + sum(xs)
        if not any(base + sum(ys) == 0 for ys in itertools.product(*exist)):
            return False
    return True


agree = total = 0
for _ in range(150 if QUICK else 600):
    n = rng.randint(2, 5)
    M = []
    for i in range(n):
        u, v = rng.sample(range(-4, 5), 2)
        k = rng.randint(0, n)
        row = [u] * k + [v] * (n - k)
        rng.shuffle(row)
        M.append(row)
    total += 1
    agree += wins(M) == two_valued_formula(M)
check(
    "two-valued rows: literal game = quantified sum formula",
    agree == total,
    f"{agree}/{total}",
)


# ------------------------------------------------------------------ 5. the subset-sum embedding
def embed(us, vs, T, upper_existential=False):
    p, q = len(us), len(vs)
    m = max(p + 1, q, 1)
    n = 2 * m
    M = [[-T] * n]
    for u0, u1 in us:
        M.append([u0] * m + [u1] * m)
    while len(M) < m:
        M.append([0] * n)
    lower = [[v0] * m + [v1] * m for (v0, v1) in vs]
    if (
        upper_existential
    ):  # mutant: put the existential choices where the Enemy can force them
        M = M[:1] + lower + M[1:]
        M = M[:m]
        lower = [[u0] * m + [u1] * m for (u0, u1) in us]
    M += lower
    while len(M) < n:
        M.append([0] * n)
    return M


def qsum_true(us, vs, T) -> bool:
    return all(
        any(sum(xs) + sum(ys) == T for ys in itertools.product(*vs))
        for xs in itertools.product(*us)
    )


agree = total = mutant_caught = ntrue = 0
for _ in range(25 if QUICK else 80):
    p, q = rng.choice([(1, 1), (1, 2), (2, 1), (2, 2)])
    want = rng.random() < 0.5
    for _try in range(400):  # resample until the instance has the wanted truth value
        us = [tuple(rng.sample(range(4), 2)) for _ in range(p)]
        vs = [tuple(rng.sample(range(4), 2)) for _ in range(q)]
        T = rng.randint(0, 8)
        if qsum_true(us, vs, T) == want:
            break
    truth = qsum_true(us, vs, T)
    ntrue += truth
    total += 1
    agree += wins(embed(us, vs, T)) == truth
    mutant_caught += wins(embed(us, vs, T, upper_existential=True)) != truth
check(
    "subset-sum embedding: matrix wins iff the forall-exists sum holds",
    agree == total,
    f"{agree}/{total}, {ntrue} true",
)
check(
    "  mutant (existential rows in the upper half) disagrees somewhere",
    mutant_caught > 0,
    f"{mutant_caught} cases",
)


# ------------------------------------------------------------------ 6. families at every order
def paired(n):
    r = n // 2
    cs = [rng.randint(-5, 5) for _ in range(r - 1)]
    cs.append(-sum(cs))
    M = [None] * n
    for i in range(r):
        x = [rng.randint(-9, 9) for _ in range(n)]
        M[i] = x
        y = [cs[i] - t for t in x]
        rng.shuffle(y)
        M[n - 1 - i] = y
    return M


def hall(n):
    rs = [rng.randint(-5, 5) for _ in range(n)]
    cs = [rng.randint(-5, 5) for _ in range(n - 1)]
    cs.append(-sum(rs) - sum(cs))
    M = []
    for i in range(n):
        row = [rs[i] + c for c in cs]
        rng.shuffle(row)
        M.append(row)
    return M


def dominant(n):
    bs = [rng.randint(-5, 5) for _ in range(n - 1)]
    bs.append(-sum(bs))
    M = []
    for i in range(
        n
    ):  # row i+1: n - (i+1) + 1 copies of b, the other i entries arbitrary
        row = [bs[i]] * (n - i) + [rng.randint(-9, 9) for _ in range(i)]
        rng.shuffle(row)
        M.append(row)
    return M


for name, fam, orders in [
    ("paired rows", paired, (4, 6)),
    ("Hall", hall, (3, 4, 5)),
    ("repeated value", dominant, (3, 4, 5)),
]:
    ok = all(wins(fam(n)) for n in orders for _ in range(3 if QUICK else 8))
    check(f"family '{name}' is winning (orders {orders})", ok)
check(
    "  parameter counts: paired r*n + r - 1 = n(n+1)/2 - 1; repeated (n-1) + sum(i-1) = n(n+1)/2 - 1",
    all(n // 2 * n + n // 2 - 1 == n * (n + 1) // 2 - 1 for n in (2, 4, 6, 8, 10))
    and all(
        (n - 1) + sum(i - 1 for i in range(1, n + 1)) == n * (n + 1) // 2 - 1
        for n in range(1, 11)
    ),
)
# mutant: Hall family with one row shifted is losing for some instance
caught = False
for _ in range(30):
    M = hall(4)
    M[2] = [t + 1 for t in M[2]]
    caught |= not wins(M)
check("  mutant (Hall row shifted by 1) loses", caught)

print()
print("ALL PASS" if not FAIL else f"FAILURES: {FAIL}")
sys.exit(1 if FAIL else 0)
