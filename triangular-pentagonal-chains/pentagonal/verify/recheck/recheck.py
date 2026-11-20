"""Independent recheck for the pentagonal case (no code shared with base_gen.c / layout_cp.py / small_cases.py).

Generalized pentagonal numbers P_k = k(3k-1)/2, k in Z. Good chain of length m: 1..m in some order, from 3 to
2 (m even) / 19 (m odd), adjacent sums odd generalized pentagonal. Inflation f_c(v) = 49v + (c if v odd else 2 - c),
offsets -23..25, glue 1..25, N = 49n + r with 26 <= r <= 74.
Checks: (1) base 60..2965; (2) step conditions S1-S5 for all 98 layouts; (3) small certificates; rebuild sample."""
from __future__ import annotations
import gzip, json, random, sys
from pathlib import Path

V = Path(__file__).resolve().parent.parent
PENT = set()
for k in range(-3000, 3001):
    PENT.add(k * (3 * k - 1) // 2)
START, M0, TOP = 3, 60, 49 * 60 + 25


def opent(s: int) -> bool:
    return s % 2 == 1 and s in PENT


def end_of(m: int) -> int:
    return 2 if m % 2 == 0 else 19


assert all((49 * (k * (3 * k - 1) // 2) + 2) in PENT for k in range(-50, 51))  # 49 P_k + 2 = P_(7k-1)

base = {}
with gzip.open(V / "base_chains.txt.gz", "rt") as f:
    for line in f:
        a = list(map(int, line.split()))
        base[a[0]] = a[1:]
for m in range(M0, TOP + 1):
    assert m in base, f"no base chain for {m}"
    c = base[m]
    assert len(c) == m and sorted(c) == list(range(1, m + 1)), m
    assert c[0] == START and c[-1] == end_of(m), m
    assert all(opent(x + y) for x, y in zip(c, c[1:])), m
assert (START + 2) in PENT and (START + 19) in PENT  # closure: 5 and 22
print("(1) base chains OK for", M0, "..", TOP)

L = json.loads((V / "layouts.json").read_text())["layouts"]
assert len(L) == 98
for r in range(26, 75):
    for p in (0, 1):
        items = L[f"{r},{p}"]
        K = r - 49
        glue = [it[1] for it in items if it[0] == "g"]
        blks = [(it[1][0], it[1][1], it[2]) for it in items if it[0] == "b"]
        assert sorted(glue) == list(range(1, 26)), (r, p)                                  # S1
        assert items[0] == ["g", START] and items[-1] == ["g", end_of(p + r)], (r, p)
        assert sorted(c for c, _, _ in blks) == list(range(-23, 26)), (r, p)               # S2
        assert sum(1 for _, w, _ in blks if w == "t") == r - 25, (r, p)                    # S3
        for c, w, _ in blks:                                                               # S4
            if w == "t":
                assert (c if (p + 1) % 2 == 1 else 2 - c) <= K, (r, p, c)
        def ends(c, w, rev):
            lp = p if w == "s" else 1 - p
            fv = lambda v: 49 * v + (c if v % 2 else 2 - c)
            first, last = fv(START), fv(end_of(lp))
            return (last, first) if rev else (first, last)
        seq = [(it[1], it[1]) if it[0] == "g" else ends(it[1][0], it[1][1], it[2]) for it in items]
        assert all(opent(a[1] + b[0]) for a, b in zip(seq, seq[1:])), (r, p)               # S5
print("(2) all 98 layouts satisfy S1-S5")

S = json.loads((V / "small_certificates.json").read_text())
for n, c in S["chains"].items():
    n = int(n); assert sorted(c) == list(range(1, n + 1)) and all((x + y) in PENT for x, y in zip(c, c[1:])), n
for n, c in S["necklaces"].items():
    n = int(n); assert sorted(c) == list(range(1, n + 1)) and all((x + y) in PENT for x, y in zip(c, c[1:] + c[:1])), n
assert sorted(map(int, S["chains"])) == list(range(4, 60))
assert sorted(map(int, S["necklaces"])) == list(range(9, 60))
print("(3) small certificates OK")

memo = {}
def C(N):
    if N <= TOP:
        return base[N]
    if N in memo:
        return memo[N]
    n = (N - 26) // 49; r = N - 49 * n; p = n % 2
    s, t = C(n), C(n + 1)
    out = []
    for it in L[f"{r},{p}"]:
        if it[0] == "g":
            out.append(it[1]); continue
        c, w = it[1]; x = s if w == "s" else t
        b = [49 * v + (c if v % 2 else 2 - c) for v in x]
        out += b[::-1] if it[2] else b
    memo[N] = out
    return out

rng = random.Random(int(sys.argv[1]) if len(sys.argv) > 1 else 5)
for N in [TOP + 1, TOP + 2, TOP + 49, 6000] + [rng.randrange(TOP + 1, 200000) for _ in range(5)]:
    c = C(N)
    assert len(c) == N and set(c) == set(range(1, N + 1)) and all(opent(x + y) for x, y in zip(c, c[1:])), N
    assert c[0] == START and c[-1] == end_of(N) and (c[-1] + c[0]) in PENT
print("rebuild sample OK")
