"""Check the explicit formula for P_i proved in the note against an independent direct computation.
Direct: P_i = (1-x)^i (x^i S_{-i} - C^{-i} S_0), power series from Mahonian rows (truncated, exact integers).
Formula (note, Theorem 1):
  P_i = (1-x)^i [ sum_{n=0}^{i-2} c_n x^{n+i} - sum_{r=1}^{i} a_r x^{i-r} ]
        + x^i sum_{t=0}^{i-1} [ f_t (1-x)^{i-1} + sum_{s<t} f_s x (1-x)^{i-t+s-1} ],
  a_r = [q^{i-r}] F(q)(1-q)^r,  c_n = I_n(n+i) - A(n,n+i) - sum_{t<i} A(n,t),  A(n,k) = [q^k] F(q)(1-q)^{-n}.
Also asserts deg P_i = 3i-2 with leading coefficient (-1)^i (i >= 2) and c_{i-2} = 1."""
from math import comb
X = 70; NM = X + 8; QM = 2 * NM + 10
def mahonian(n):
    row = [1]
    for j in range(1, n + 1):
        new = [0] * (len(row) + j - 1)
        for a, v in enumerate(row):
            for t in range(j): new[a + t] += v
        row = new
    return row
rows = [mahonian(n) for n in range(NM + 1)]
I = lambda n, k: rows[n][k] if 0 <= k < len(rows[n]) else 0
F = [0] * (QM + 1); F[0] = 1
for j in range(1, QM + 1):
    for k in range(QM, j - 1, -1): F[k] -= F[k - j]
def A(n, k): return F[k] if n == 0 else (sum(F[s] * comb(n - 1 + k - s, k - s) for s in range(k + 1)) if k >= 0 else 0)
def mul(a, b, L=X):
    c = [0] * L
    for i, u in enumerate(a[:L]):
        if u:
            for j, v in enumerate(b[:L - i]): c[i + j] += u * v
    return c
def pw(p, e, L=X):
    out = [1] + [0] * (L - 1)
    for _ in range(e): out = mul(out, p, L)
    return out
cat = [comb(2 * n, n) // (n + 1) for n in range(X)]
Cinv = [1] + [-cat[n - 1] for n in range(1, X)]
S0 = [I(n, n) for n in range(X)]
one_minus_x = [1, -1]
# P_1..P_4 as printed in Claesson-Franklin-Steingrimsson, EJC 30(4) (2023) P4.7, Sec. 5 (coefficients from x^0)
PUBLISHED = {1: [-1, 2], 2: [-1, 4, -4, 1, 1], 3: [-1, 6, -12, 10, -2, -1, 2, -1],
             4: [-1, 8, -24, 35, -25, 6, 4, -3, 3, -3, 1]}
for i in range(1, 9):
    direct = mul(pw(one_minus_x, i), [a - b for a, b in zip([0] * i + [I(n, n + i) for n in range(X - i)], mul(S0, pw(Cinv, i)))])
    T = X - 3 * i - 5                                    # trust window
    a = {r: sum(F[s] * ((-1) ** (i - r - s)) * comb(r, i - r - s) for s in range(i - r + 1)) for r in range(1, i + 1)}
    c = {n: I(n, n + i) - A(n, n + i) - sum(A(n, t) for t in range(i)) for n in range(0, i - 1)}
    inner = [0] * X
    for n, v in c.items(): inner[n + i] += v
    for r, v in a.items(): inner[i - r] -= v
    formula = mul(pw(one_minus_x, i), inner)
    for t in range(i):
        part = [F[t] * v for v in pw(one_minus_x, i - 1)]
        for s in range(t):
            part = [p + q for p, q in zip(part, mul([0, F[s]], pw(one_minus_x, i - t + s - 1)))]
        formula = [p + q for p, q in zip(formula, [0] * i + part[:X - i])]
    assert direct[:T] == formula[:T], f"formula mismatch at i={i}"
    deg = max(k for k in range(T) if formula[k])
    if i >= 2:
        assert c[i - 2] == 1 and deg == 3 * i - 2 and formula[deg] == (-1) ** i, (i, c.get(i - 2), deg)
    if i in PUBLISHED:
        assert formula[:deg + 1] == PUBLISHED[i], f"P_{i} differs from the printed one in CFS"
    print(f"i={i}: explicit formula == direct (x^0..x^{T-1}); deg {deg} = 3i-2; lead {formula[deg]}; c_(i-2) = {c.get(i-2)}")
