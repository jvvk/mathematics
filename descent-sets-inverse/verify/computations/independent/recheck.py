"""J4 independent recheck for the EJC manuscript (MO 486548). Shares no code with the scripts
that produced the paper's numbers. Each claim is checked from first principles:
SYT are enumerated directly, RSK is reimplemented, Stanley's generating function is expanded
in exact rational arithmetic, and the sampling certifier is rewritten from Lemmas 3.1-3.2."""
import json, math, random, re, sys
from fractions import Fraction
from functools import lru_cache
from itertools import combinations, permutations

OUT = {}
def claim(key, ok, detail):
    OUT[key] = {"pass": bool(ok), "detail": detail}
    print(("PASS " if ok else "FAIL ") + key + ": " + str(detail), flush=True)

# ---------- basic arithmetic claims
OEIS = [1, 2, 6, 22, 94, 426, 1938, 8724, 38724, 169438, 731390, 3119052, 13162228]   # f(1..13)
claim("f13_root", round(OEIS[12] ** (1 / 13), 2) == 3.53, OEIS[12] ** (1 / 13))
claim("f13_ratio", round(OEIS[12] / 4 ** 12, 3) == 0.785, OEIS[12] / 4 ** 12)
claim("block_bound_eq_n2", 4 - 3 + 1 == OEIS[1], "f(2)=2=4^1-3^1+1")
F20 = 260283514168  # exact f(20) from the independent C++ enumeration (conjectures-20261007/n20.json)
claim("fail20", round(1 - F20 / 4 ** 19, 5) == 0.05309, 1 - F20 / 4 ** 19)

# ---------- descent sets
def des(w): return {i + 1 for i in range(len(w) - 1) if w[i] > w[i + 1]}
def inv(w):
    r = [0] * len(w)
    for i, v in enumerate(w): r[v - 1] = i + 1
    return r
claim("example_52314", des([5, 2, 3, 1, 4]) == {1, 3} and des(inv([5, 2, 3, 1, 4])) == {1, 4},
      (des([5, 2, 3, 1, 4]), des(inv([5, 2, 3, 1, 4]))))
claim("n3_pairs", sorted((tuple(sorted(des(w))), tuple(sorted(des(inv(list(w)))))) for w in permutations([1, 2, 3]))
      == sorted([((), ()), ((2,), (1,)), ((2,), (2,)), ((1,), (2,)), ((1,), (1,)), ((1, 2), (1, 2))]), "six pairs")

# ---------- RSK (row insertion), fresh implementation
def rsk(w):
    P, Q = [], []
    for k, x in enumerate(w, 1):
        r = 0
        while True:
            if r == len(P):
                P.append([x]); Q.append([k]); break
            row = P[r]
            j = next((j for j, y in enumerate(row) if y > x), None)
            if j is None:
                row.append(x); Q[r].append(k); break
            row[j], x = x, row[j]
            r += 1
    return P, Q
def tdes(T):
    row = {v: r for r, R in enumerate(T) for v in R}
    n = len(row)
    return {i for i in range(1, n) if row[i + 1] > row[i]}
w = [1, 4, 5, 7, 14, 11, 13, 10, 6, 8, 9, 3, 12, 2]
P, Q = rsk(w)
figQ = [[1, 2, 3, 4, 5, 7, 13], [6, 10, 11], [8], [9], [12], [14]]
figP = [[1, 2, 5, 6, 8, 9, 12], [3, 10, 13], [4], [7], [11], [14]]
S14, T14 = {5, 7, 8, 11, 13}, {2, 3, 6, 9, 10, 12, 13}
claim("figure1_rsk", P == figP and Q == figQ and des(w) == S14 and des(inv(w)) == T14
      and tdes(Q) == S14 and tdes(P) == T14, (P == figP, Q == figQ))

# Figure 2 row words, parsed from the TikZ source
src = open(sys.argv[1] if len(sys.argv) > 1 else "../figs/rowwords.tex").read()
def word_at(y):
    vals = {}
    for m in re.finditer(r"\\node\[(?P<opt>[^\]]*)\] at \((?P<x>[\d.]+),(?P<y>-?[\d.]+)\) \{\$(?P<v>\d+)\$\}", src):
        if "scriptsize" in m.group("opt") and "bfseries" not in m.group("opt"): continue
        if abs(float(m.group("y")) - y) < 1e-6: vals[float(m.group("x"))] = int(m.group("v"))
    return [vals[k] for k in sorted(vals)]
wS, wT = word_at(-0.35), word_at(-3.5500000000000003)
def rowword(T):
    row = {v: r + 1 for r, R in enumerate(T) for v in R}
    return [row[i] for i in range(1, len(row) + 1)]
def lattice(u):
    c = {}
    for x in u:
        c[x] = c.get(x, 0) + 1
        if x > 1 and c[x] > c.get(x - 1, 0): return False
    return True
asc = lambda u: {i + 1 for i in range(len(u) - 1) if u[i] < u[i + 1]}
claim("figure2_words", wS == rowword(figQ) and wT == rowword(figP) and lattice(wS) and lattice(wT)
      and asc(wS) == S14 and asc(wT) == T14, (wS, wT))

# ---------- SYT enumeration by descent set
def syt_by_descent(n):
    """dict: frozenset(descent set) -> {shape: count}"""
    out = {}
    def rec(shape, rows_of, k):
        if k > n:
            D = frozenset(i for i in range(1, n) if rows_of[i] > rows_of[i - 1])
            d = out.setdefault(D, {})
            key = tuple(shape)
            d[key] = d.get(key, 0) + 1
            return
        for r in range(len(shape) + 1):
            if r == len(shape) or (r == 0 or shape[r] < shape[r - 1]):
                if r == len(shape): shape.append(1)
                else: shape[r] += 1
                rows_of.append(r); rec(shape, rows_of, k + 1); rows_of.pop()
                if shape[r] == 1 and r == len(shape) - 1: shape.pop()
                else: shape[r] -= 1
    rec([], [], 1)
    return out

def partitions(n, mx=None):
    if mx is None: mx = n
    if n == 0: yield (); return
    for k in range(min(n, mx), 0, -1):
        for p in partitions(n - k, k): yield (k,) + p
def dom(a, b):  # a <= b in dominance
    sa = sb = 0
    for i in range(max(len(a), len(b))):
        sa += a[i] if i < len(a) else 0; sb += b[i] if i < len(b) else 0
        if sa > sb: return False
    return True
def comp(S, n):
    cuts = [0] + sorted(S) + [n]
    return [cuts[i + 1] - cuts[i] for i in range(len(cuts) - 1)]
def conj(p):
    return tuple(sum(1 for x in p if x > i) for i in range(p[0])) if p else ()
def ribbon_cols(alpha):
    # column lengths of the ribbon with row lengths alpha, rows overlapping in one column
    cols = []
    for i, a in enumerate(alpha):
        if i == 0: cols += [1] * a
        else: cols[-1] += 1; cols += [1] * (a - 1)
    return tuple(sorted(cols, reverse=True))

# ribbon supports at n=6 and n=11
for n, expect in ((6, 4), (11, 544)):
    tab = syt_by_descent(n); parts = list(partitions(n))
    bad = 0
    for k in range(n):
        for S in combinations(range(1, n), k):
            a = comp(S, n); lo = tuple(sorted(a, reverse=True)); hi = conj(ribbon_cols(a))
            interval = {p for p in parts if dom(lo, p) and dom(p, hi)}
            supp = set(tab.get(frozenset(S), {}))
            assert supp <= interval
            bad += supp != interval
    claim(f"nonfull_support_n{n}", bad == expect, f"{bad} (paper {expect})")
tab6 = syt_by_descent(6)
claim("ribbon_123_misses_33", (3, 3) not in tab6[frozenset({1, 3})] and dom((3, 2, 1), (3, 3)) and dom((3, 3), (4, 2))
      and conj(ribbon_cols([1, 2, 3])) == (4, 2), sorted(tab6[frozenset({1, 3})]))

# ---------- Table: proportion of occurring pairs by ||S|-|T||, and f(11), f(12)
for n, row in ((11, [1, 0.940, 0.702, 0.319, 0.056, 0.002]), (12, [1, 0.966, 0.807, 0.481, 0.152, 0.015])):
    tab = syt_by_descent(n); parts = {p: i for i, p in enumerate(partitions(n))}
    sets = [frozenset(S) for k in range(n) for S in combinations(range(1, n), k)]
    mask = {S: sum(1 << parts[p] for p in tab.get(S, {})) for S in sets}
    occ = {}; tot = {}; f = 0
    for S in sets:
        for T in sets:
            d = abs(len(S) - len(T)); hit = (mask[S] & mask[T]) != 0
            tot[d] = tot.get(d, 0) + 1; occ[d] = occ.get(d, 0) + hit; f += hit
    got = [round(occ[d] / tot[d], 3) for d in range(6)]
    claim(f"table_n{n}", got == row and f == OEIS[n - 1], f"{got} f={f}")

# ---------- 1808 and 1751 at n=11
tab11 = syt_by_descent(11)
beta = lambda S: sum(c * c for c in tab11.get(frozenset(S), {}).values())
S0 = {2, 4, 7, 9}
nb = set()
for x in range(1, 11):
    nb.add(frozenset(S0 ^ {x}))
for x in S0:
    for y in (x - 1, x + 1):
        if 1 <= y <= 10 and y not in S0: nb.add(frozenset((S0 - {x}) | {y}))
nb.discard(frozenset(S0))
claim("local_max_1808_1751", beta(S0) == 1808 and max(beta(T) for T in nb) == 1751,
      (beta(S0), max(beta(T) for T in nb)))

# ---------- Gessel diagonal maxima n<=11 (independent of diag.py and search.cpp)
A007999 = {4: 2, 5: 3, 6: 8, 7: 19, 8: 64, 9: 213, 10: 880, 11: 3717}
ok = True
for n in range(4, 12):
    t = syt_by_descent(n)
    vals = {S: sum(c * c for c in d.values()) for S, d in t.items()}
    M = max(vals.values()); arg = {S for S, v in vals.items() if v == M}
    alt1 = frozenset(range(1, n, 2)); alt2 = frozenset(range(2, n, 2))
    ok &= M == A007999[n] and arg == {alt1, alt2}
claim("gessel_max_n4_11", ok, "maxima only at alternating sets, values = A007999")

# ---------- g(n) numerics from Stanley's generating function, exact rationals
def euler_numbers(N):
    # boustrophedon (Seidel-Entringer) triangle
    E = [1]; row = [1]
    for n in range(1, N + 1):
        new = [0]
        for k in range(1, n + 1): new.append(new[-1] + row[n - k])
        row = new; E.append(row[-1])
    return E
NMAX = 159
E = euler_numbers(NMAX + 1)
claim("euler_small", E[:11] == [1, 1, 1, 2, 5, 16, 61, 272, 1385, 7936, 50521], E[:11])
u = [Fraction(0)] * (NMAX + 1)
for k in range(1, NMAX + 1, 2): u[k] = Fraction(1, k)
def mul(a, b):
    c = [Fraction(0)] * (NMAX + 1)
    for i, x in enumerate(a):
        if x:
            for j in range(NMAX + 1 - i):
                if b[j]: c[i + j] += x * b[j]
    return c
s = [Fraction(0)] * (NMAX + 1)  # (1-x^2)^(-1/2) = sum C(2j,j) x^(2j) / 4^j
for j in range(0, NMAX // 2 + 1): s[2 * j] = Fraction(math.comb(2 * j, j), 4 ** j)
odd = [Fraction(0)] * (NMAX + 1); even = [Fraction(0)] * (NMAX + 1)
power = [Fraction(0)] * (NMAX + 1); power[0] = Fraction(1)
for m in range(0, NMAX + 1):
    coef = Fraction(E[m] ** 2, math.factorial(m))
    tgt = odd if m % 2 else even
    for i in range(NMAX + 1):
        if power[i]: tgt[i] += coef * power[i]
    power = mul(power, u)
G = [o + e for o, e in zip(odd, mul(s, even))]
g = [int(x) if x.denominator == 1 else None for x in G]
claim("g_small", g[:12] == [1, 1, 1, 1, 2, 3, 8, 19, 64, 213, 880, 3717], g[:12])
vals = {n: n * (Fraction(g[n] * math.factorial(n), E[n] ** 2) - 1) for n in (40, 80, 159)}
got = {n: round(float(v), 4) for n, v in vals.items()}
claim("g_numerics", got == {40: 2.1130, 80: 2.0694, 159: 2.0296} and round(math.pi ** 4 / 48, 4) == 2.0294, got)

# ---------- sampling: certifier rewritten from Lemmas 3.1-3.2 and Corollary 3.3
def stats(X, n):
    m = n // 2
    starts = [1] + [x + 1 for x in sorted(X)]
    lens = [b - a for a, b in zip(starts, starts[1:] + [n + 1])]
    A = sum(1 for p in range(1, m) if p not in X)
    late = [j for j in range(2, len(starts)) if starts[j] > m]
    cap_extra = sum(lens[j] - 1 for j in late)
    cap_two = sum(1 for j in late if lens[j - 1] >= 2)
    return A, cap_extra, cap_two
def certified(S, T, n):
    if len(S) > len(T): S, T = T, S
    s, t = len(S), len(T)
    if s == t: return True
    c, b = s - 1, t - s + 1
    if s < 1 or n - c - b < b: return False
    AS, extraS, _ = stats(S, n); AT, _, twoT = stats(T, n)
    return AS >= b and AT >= b and extraS >= b - 1 and twoT >= b - 1
rng = random.Random(11); res = {}
for n in [12, 13, 20, 50, 100, 200, 400]:
    ok = 0
    for _ in range(20000):
        S = {i for i in range(1, n) if rng.random() < .5}
        T = {i for i in range(1, n) if rng.random() < .5}
        ok += certified(S, T, n)
    res[n] = ok
props = {n: res[n] / 20000 for n in res}
fail400 = 20000 - res[400]
z = 1.959963984540054; p = fail400 / 20000; den = 1 + z * z / 20000
cen = (p + z * z / 40000) / den; dl = z * math.sqrt(p * (1 - p) / 20000 + z * z / (4 * 20000 ** 2)) / den
stated = {50: 0.80, 100: 0.93, 200: 0.986, 400: 0.9995}   # as printed in Remark 3.4
digits = {50: 2, 100: 2, 200: 3, 400: 4}
claim("sampling", all(abs(props[k] - v) <= 0.5 * 10 ** -digits[k] + 1e-12 for k, v in stated.items())
      and fail400 == 11 and abs(p - 0.00055) <= 5e-6 and abs(cen - dl - 0.00031) <= 5e-6 and abs(cen + dl - 0.00098) <= 5e-6,
      (props, fail400, [cen - dl, cen + dl]))

json.dump(OUT, open("recheck.json", "w"), indent=1, default=str)
print("ALL PASS" if all(v["pass"] for v in OUT.values()) else "SOME FAIL")
