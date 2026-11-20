"""Independent recheck (no code shared with assemble.py / layout_cp.py / base_gen.c).

Checks the three finite ingredients of the proof:
  (1) base: for 54 <= m <= 2673 a chain on [1..m] from 1 to 2 (m even) / 9 (m odd), adjacent sums odd triangular;
  (2) each of the 98 layouts satisfies the step conditions S1-S6 (stated in the paper and in Lean);
  (3) small cases: certificates for n = 2, 9..53 (chains) and 12..53 minus 14 (necklaces).
Then rebuilds C_N for a sample of N by the paper's recipe and checks it directly."""
from __future__ import annotations
import gzip, json, random, sys
from pathlib import Path

V = Path(__file__).resolve().parent.parent
TRI = set()
k = 0
while k * (k + 1) // 2 <= 10**7:
    TRI.add(k * (k + 1) // 2); k += 1


def otri(s: int) -> bool:
    return s % 2 == 1 and s in TRI


def end_of(m: int) -> int:
    return 2 if m % 2 == 0 else 9


# (1) base
base = {}
with gzip.open(V / "base_chains.txt.gz", "rt") as f:
    for line in f:
        a = list(map(int, line.split()))
        base[a[0]] = a[1:]
for m in range(54, 2674):
    assert m in base, f"no base chain for {m}"
    c = base[m]
    assert len(c) == m and sorted(c) == list(range(1, m + 1)), m
    assert c[0] == 1 and c[-1] == end_of(m), m
    assert all(otri(x + y) for x, y in zip(c, c[1:])), m
print("(1) base chains OK for 54..2673")

# (2) layouts
L = json.loads((V / "layouts.json").read_text())["layouts"]
assert len(L) == 98
for r in range(28, 77):
    for p in (0, 1):
        items = L[f"{r},{p}"]
        K = r - 49
        glue = [it[1] for it in items if it[0] == "g"]
        blks = [(it[1][0], it[1][1], it[2]) for it in items if it[0] == "b"]
        # S1 glue numbers are exactly 1..27; first item is glue 1, last is glue end(N)
        assert sorted(glue) == list(range(1, 28)), (r, p)
        assert items[0] == ["g", 1] and items[-1] == ["g", end_of(p + r)], (r, p)
        # S2 block offsets are exactly -21..27, each once
        assert sorted(c for c, _, _ in blks) == list(range(-21, 28)), (r, p)
        # S3 number of t-blocks is r - 27 (so the total length is 27 + 49 n + (r - 27) = N)
        assert sum(1 for _, w, _ in blks if w == "t") == r - 27, (r, p)
        # S4 the extra value of a t-block, 49(n+1) + (c if n+1 odd else 6-c), is <= N, i.e. its offset is <= K
        for c, w, _ in blks:
            if w == "t":
                top_off = c if (p + 1) % 2 == 1 else 6 - c
                assert top_off <= K, (r, p, c)
        # S5 junction sums are odd triangular (block ends: first 49*1+c; last 49*end(len)+(c if len odd else 6-c))
        def ends(c, w, rev):
            lp = p if w == "s" else 1 - p
            first, last = 49 + c, 49 * end_of(lp) + (c if lp == 1 else 6 - c)
            return (last, first) if rev else (first, last)
        seq = []
        for it in items:
            if it[0] == "g":
                seq.append((it[1], it[1]))
            else:
                seq.append(ends(it[1][0], it[1][1], it[2]))
        assert all(otri(a[1] + b[0]) for a, b in zip(seq, seq[1:])), (r, p)
print("(2) all 98 layouts satisfy S1-S5")

# (3) small cases
S = json.loads((V / "small_certificates.json").read_text())
for n, c in S["chains"].items():
    n = int(n); assert sorted(c) == list(range(1, n + 1)) and all((x + y) in TRI for x, y in zip(c, c[1:])), n
for n, c in S["necklaces"].items():
    n = int(n); assert sorted(c) == list(range(1, n + 1)) and all((x + y) in TRI for x, y in zip(c, c[1:] + c[:1])), n
assert sorted(map(int, S["chains"])) == [2] + list(range(9, 54))
assert sorted(map(int, S["necklaces"])) == [n for n in range(12, 54) if n != 14]
print("(3) small certificates OK")

# rebuild sample (independent implementation of the recipe)
memo = {}
def C(N):
    if N <= 2673:
        return base[N]
    if N in memo:
        return memo[N]
    n = (N - 28) // 49; r = N - 49 * n; p = n % 2
    s, t = C(n), C(n + 1)
    out = []
    for it in L[f"{r},{p}"]:
        if it[0] == "g":
            out.append(it[1]); continue
        c, w = it[1]; x = s if w == "s" else t
        b = [49 * v + (c if i % 2 == 0 else 6 - c) for i, v in enumerate(x)]
        out += b[::-1] if it[2] else b
    memo[N] = out
    return out

rng = random.Random(int(sys.argv[1]) if len(sys.argv) > 1 else 3)
for N in [2674, 2675, 2722, 5000] + [rng.randrange(2674, 200000) for _ in range(5)]:
    c = C(N)
    assert len(c) == N and set(c) == set(range(1, N + 1)) and all(otri(x + y) for x, y in zip(c, c[1:])), N
    assert c[0] == 1 and c[-1] == end_of(N) and (1 + end_of(N)) in TRI
print("rebuild sample OK")
