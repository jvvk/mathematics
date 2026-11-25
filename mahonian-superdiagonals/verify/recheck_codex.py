"""Independent exact audit; does not import either supplied check script.

Run: python3 recheck_codex.py
All arrays store coefficients in increasing order, truncated to LEN terms.
"""
from itertools import permutations

LEN = 160
KMAX = 240
NMAX = 160
IMAX = 80


def mul(a, b, length=LEN):
    out = [0] * length
    for j, u in enumerate(a[:length]):
        if u:
            for k, v in enumerate(b[:length-j]):
                if v:
                    out[j+k] += u*v
    return out


def inverse(a):
    assert a[0] == 1
    out = [1] + [0]*(LEN-1)
    for k in range(1, LEN):
        out[k] = -sum(a[j]*out[k-j] for j in range(1, min(k+1, len(a))))
    return out


def difference(a):
    return [a[k] - (a[k-1] if k else 0) for k in range(len(a))]


def prefix(a):
    out = []
    acc = 0
    for v in a:
        acc += v
        out.append(acc)
    return out


# Mahonian rows by a sliding-sum recurrence, capped only above KMAX.
rows = [[1] + [0]*KMAX]
for n in range(1, NMAX+1):
    prev = rows[-1]
    row = []
    acc = 0
    for k in range(KMAX+1):
        acc += prev[k] - (prev[k-n] if k >= n else 0)
        row.append(acc)
    rows.append(row)

total_permutations = 0
for n in range(9):
    counts = [0]*(n*(n-1)//2+1)
    for p in permutations(range(n)):
        k = sum(p[a] > p[b] for a in range(n) for b in range(a+1, n))
        counts[k] += 1
        total_permutations += 1
    assert counts == rows[n][:len(counts)]
    assert not any(rows[n][len(counts):])
print(f"Permutation enumeration: n=0..8, {total_permutations} permutations; PASS")

# Euler coefficients by pentagonal numbers, cross-checked against the product.
F = [0]*(KMAX+1)
F[0] = 1
j = 1
while j*(3*j-1)//2 <= KMAX:
    for k in (j*(3*j-1)//2, j*(3*j+1)//2):
        if k <= KMAX:
            F[k] = (-1)**j
    j += 1
product = [1] + [0]*KMAX
for j in range(1, KMAX+1):
    product = [v - (product[k-j] if k >= j else 0) for k, v in enumerate(product)]
assert product == F
print("Euler coefficients: pentagonal formula vs finite product, degrees 0..240; PASS")

# A(n,k) tables by formal multiplication/division by 1-q, no binomials.
Atab = {0: F}
for n in range(1, NMAX+1):
    Atab[n] = prefix(Atab[n-1])
for r in range(1, IMAX+1):
    Atab[-r] = difference(Atab[1-r])


def A(n, k):
    return Atab[n][k] if k >= 0 else 0


def c(n, i):
    return rows[n][n+i] - A(n, n+i) - sum(Atab[n][:i])


# Enumerate actual integer partitions, not just their generating function.
def partitions(m, lo=1):
    if not m:
        yield ()
    else:
        for a in range(lo, m+1):
            for tail in partitions(m-a, a):
                yield (a,) + tail


partition_counts = [[0]*36 for _ in range(17)]
total_partitions = 0
for m in range(36):
    for p in partitions(m):
        total_partitions += 1
        for n in range(17):
            if not p or p[0] > n:
                partition_counts[n][m] += 1
for n in range(17):
    dp = [1]+[0]*35
    for part in range(n+1, 36):
        for m in range(part, 36):
            dp[m] += dp[m-part]
    assert dp == partition_counts[n]
    assert dp[0] == 1 and all(dp[m] == 0 for m in range(1, n+1))
    assert all(dp[m] == 1 for m in range(n+1, 2*n+2))
    assert dp[2*n+2] == 2
print(f"Partition enumeration: m=0..35, n=0..16, {total_partitions} partitions; all claimed counts PASS")

assert all(rows[n][n] == A(n, n) for n in range(NMAX+1))
assert all(c(n, i) == 0 for i in range(1, IMAX+1) for n in range(i-1, NMAX+1))
assert all(c(i-2, i) == 1 for i in range(2, IMAX+1))
print("Lemma 2 and i=0 identity: i=1..80, n=i-1..160; c_(i-2)=1 for i=2..80; PASS")
print("Early correction vectors [c_0,...,c_(i-2)], i=2..8:",
      [[c(n, i) for n in range(i-1)] for i in range(2, 9)])

# Catalan series using its defining recursion, then a generic series inverse.
C = [1] + [0]*(LEN-1)
for k in range(1, LEN):
    C[k] = sum(C[j]*C[k-1-j] for j in range(k))
Cinv = inverse(C)
w = [0] + C[:-1]
assert mul(w, [1-v if k == 0 else -v for k, v in enumerate(w)]) == [0, 1]+[0]*(LEN-2)

# Direct composition and inversion, independent of the Lagrange formula.
Fw = [0]*LEN
for k in range(LEN-1, -1, -1):
    Fw = mul(Fw, w)
    Fw[0] += F[k]
phi_w = inverse([1] + [-v for v in w[1:]])
phiprime_w = mul(phi_w, phi_w)
denom = [1] + [-v for v in phiprime_w[:-1]]
H = mul(Fw, inverse(denom))
assert H == [rows[n][n] for n in range(LEN)]
Ci = [1]+[0]*(LEN-1)
for i in range(41):
    if i:
        Ci = mul(Ci, Cinv)
    Hi = mul(H, Ci)  # equals x^i w^{-i} F(w)/(1-x phi'(w))
    for n in range(-i-4, 120):
        assert (Hi[n+i] if n+i >= 0 else 0) == A(n, n+i), (i, n)
print("Laurent inversion by direct composition: i=0..40, n=-i-4..119, including n=0 and all negative terms; PASS")
print("Negative Laurent coefficients [A(-r,i-r)] for r=i,...,1, i=1..4:",
      [[A(-r, i-r) for r in range(i, 0, -1)] for i in range(1, 5)])

inverse_powers = [[1]+[0]*(LEN-1)]
for d in range(1, 81):
    inverse_powers.append(prefix(inverse_powers[-1]))
for t in range(80):
    col = [F[t]*v for v in inverse_powers[1]]
    for s in range(t):
        shifted = [0]+inverse_powers[t-s+1][:-1]
        col = [u+F[s]*v for u, v in zip(col, shifted)]
    assert col == [A(n, t) for n in range(LEN)]
print("Lemma 4 rational columns: t=0..79, x-degrees 0..159; PASS")

# Compare explicit formula and degree to direct Mahonian/Catalan computation.
powers = [[1]+[0]*(LEN-1)]
for d in range(1, 41):
    powers.append(difference(powers[-1]))
S0 = [rows[n][n] for n in range(LEN)]
Ci = [1]+[0]*(LEN-1)
degrees, leads, at_one = [], [], []
for i in range(1, 41):
    Ci = mul(Ci, Cinv)
    main = [0]*i + [rows[n][n+i] for n in range(LEN-i)]
    direct = mul(powers[i], [a-b for a, b in zip(main, mul(S0, Ci))])
    inner = [0]*LEN
    for n in range(i-1):
        inner[n+i] += c(n, i)
    for r in range(1, i+1):
        inner[i-r] -= A(-r, i-r)
    explicit = mul(powers[i], inner)
    for t in range(i):
        for k, v in enumerate(powers[i-1]):
            if k+i < LEN:
                explicit[k+i] += F[t]*v
        for s in range(t):
            for k, v in enumerate(powers[i-t+s-1]):
                if k+i+1 < LEN:
                    explicit[k+i+1] += F[s]*v
    assert explicit == direct, i
    degree = max(k for k, v in enumerate(direct) if v)
    assert degree == 3*i-2
    assert direct[degree] == (2 if i == 1 else (-1)**i)
    assert all(type(v) is int for v in direct)
    assert sum(direct) == 1
    degrees.append(degree)
    leads.append(direct[degree])
    at_one.append(sum(direct))
print("P_i explicit vs direct: i=1..40, x-degrees 0..159; degree=3i-2, integral coefficients, P_i(1)=1; PASS")
print("Leading coefficients: i=1: 2; i=2..40: (-1)^i; PASS")
print("Boundary examples: p_>0(1)=1, p_>0(2)=2, c_0(i=1)=0, c_0(i=2)=1")
print("Abstract/remark check: [q^(n+1)](G_n-1)=1; c_1(i=4)=", c(1, 4), sep="")
