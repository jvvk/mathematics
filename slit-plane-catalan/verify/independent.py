"""Independent check (Claude) of Codex route r1 for Stanley 236-237. Shares no code with codex_route_r1/.
Brute-force transfer counts of slit-plane walks plus exact cyclic weights from atom words; asserts every
identity the proof uses. Exits nonzero on failure; refuses python -O."""
from __future__ import annotations
import sys
from fractions import Fraction as Fr
from functools import lru_cache
from math import comb
assert __debug__, "run without -O"

SQ = [(1, 0), (-1, 0), (0, 1), (0, -1)]
DG = [(1, 1), (1, -1), (-1, 1), (-1, -1)]
def C(n: int) -> int: return comb(2 * n, n) // (n + 1)

def counts(steps, L: int, forbid) -> list[dict]:
    """out[l][(x,y)] = walks of length l from origin avoiding forbidden points at times 1..l."""
    cur = {(0, 0): 1}; out = [dict(cur)]
    for _ in range(L):
        nxt: dict = {}
        for (x, y), c in cur.items():
            for dx, dy in steps:
                p = (x + dx, y + dy)
                if not forbid(p): nxt[p] = nxt.get(p, 0) + c
        cur = nxt; out.append(dict(cur))
    return out

strict = lambda p: p[1] == 0 and p[0] <= 0
barred = lambda p: p[1] == 0 and p[0] < 0
N = 7
S = counts(SQ, 2 * N + 2, strict); B = counts(SQ, 2 * N + 2, barred)
H = [sum(C(2 * k) * C(2 * n - 2 * k) for k in range(n + 1)) for n in range(N + 1)]
K = [sum(C(2 * k + 1) * C(2 * n - 2 * k - 1) for k in range(n)) for n in range(N + 1)]
Lm = lambda m: B[m].get((0, 0), 0)
# primitive barred loops: barred walks never at origin before the end
def primitive(m: int) -> int:
    cur = {(0, 0): 1}
    for t in range(m):
        nxt: dict = {}
        for (x, y), c in cur.items():
            for dx, dy in SQ:
                p = (x + dx, y + dy)
                if barred(p) or (p == (0, 0) and t < m - 1): continue
                nxt[p] = nxt.get(p, 0) + c
        cur = nxt
    return cur.get((0, 0), 0)
for n in range(N + 1):
    a01 = S[2 * n + 1].get((0, 1), 0)
    assert a01 == H[n] == 4 ** n * C(n), (n, a01, H[n])                       # (14),(15): 236(a)
    assert S[2 * n + 1].get((1, 0), 0) == C(2 * n + 1)                         # (7): 236(b)
    assert Lm(2 * n) == H[n] - K[n] == 2 * 4 ** n * C(n) - C(2 * n + 1)        # (10),(16): 236(e)
    assert C(2 * n + 1) == H[n] + K[n]                                          # (11)
    assert primitive(2 * n + 2) == S[2 * n + 1][(1, 0)] + 2 * a01               # closing step
    if n >= 1:
        assert primitive(2 * n) == 2 * C(2 * n - 1) + Lm(2 * n - 2)             # (13)
        assert S[2 * n].get((-1, 1), 0) * 2 == C(2 * n)                         # (18): 236(c)
        assert S[2 * n].get((1, 1), 0) == 4 ** (n - 1) * C(n) + C(2 * n) // 2   # (21): 236(d)
for m in range(1, 2 * N + 1):
    assert Lm(m) == sum((-1) ** j * C(j) * C(m - j) for j in range(m + 1))      # (9)

# cyclic weights c_s(m,i): atoms = pieces between consecutive visits to y = 0 (any x), size = length
@lru_cache(None)
def atoms(m: int) -> dict:
    """number of square-lattice atoms of length m by horizontal increment (start/end on y=0, no interior visit)."""
    out: dict = {}
    if m == 1: return {1: 1, -1: 1}
    # arch: first step N or S, return to y=0 only at the end; count by reflection: 2 * excursions in y
    cur = {(0, 1): 1}
    for t in range(m - 1):
        nxt: dict = {}
        for (x, y), c in cur.items():
            for dx, dy in SQ:
                p = (x + dx, y + dy)
                if p[1] == 0 and t < m - 2: continue
                if p[1] < 0: continue
                nxt[p] = nxt.get(p, 0) + c
        cur = nxt
    for (x, y), c in cur.items():
        if y == 0: out[x] = out.get(x, 0) + 2 * c
    return out
def cyc(m: int, d: int, sign_fn=None) -> Fr:
    """sum over atom words of total size m, increment d, of 1/(#atoms)."""
    @lru_cache(None)
    def words(rem: int, k: int) -> dict:
        if k == 0: return {0: 1} if rem == 0 else {}
        out: dict = {}
        for s in range(1, rem + 1):
            for inc, c in atoms(s).items():
                for d2, c2 in words(rem - s, k - 1).items():
                    out[inc + d2] = out.get(inc + d2, 0) + c * c2
        return out
    return sum(Fr(words(m, k).get(d, 0), k) for k in range(1, m + 1))
for m in range(1, 11):
    for i in range(-m, m + 1):
        want = Fr(comb(2 * m, m - i), m) if (m - i) % 2 == 0 else Fr(0)
        assert cyc(m, i) == want, (m, i)                                        # (6)
# exp formula (2) reproduces barred loops from c_s(m,0)
def expf(N2: int, w) -> Fr:
    @lru_cache(None)
    def f(n: int) -> Fr:  # labelled-set recursion: n f_n = sum_k k w_k f_{n-k}
        return Fr(1) if n == 0 else sum(k * w(k) * f(n - k) for k in range(1, n + 1)) / n
    return f(N2)
for m in range(0, 11):
    assert expf(m, lambda k: cyc(k, 0)) == Lm(m)
# diagonal lattice
D = counts(DG, 2 * N + 1, strict); DB = counts(DG, 2 * N, barred)
for n in range(N + 1):
    assert DB[2 * n].get((0, 0), 0) == 4 ** n * C(n)                            # (23): 237(e)
    assert D[2 * n + 1].get((1, 1), 0) + D[2 * n + 1].get((-1, 1), 0) == 2 * 4 ** n * C(n)  # (25)
    assert D[2 * n + 1].get((1, 1), 0) == C(2 * n + 1)                          # 237(a) (known)
    for i in range(1, n + 1):
        assert D[2 * n].get((2 * i, 0), 0) * n == i * comb(2 * i, i) * comb(2 * n, n - i) * 4 ** (n - i)  # (24)
print(f"ALL ROUTE-R1 IDENTITIES PASS (square/diagonal n <= {N}, cyclic weights m <= 10)")
