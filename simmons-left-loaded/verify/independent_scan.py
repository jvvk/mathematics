"""Independent exact scan (shares no code with exact_scan.py): binomial weights w_j = C(n,j) m^j (n-m)^(n-j),
alpha_i extended to i = 1..n-m, checked against the paper. Exits nonzero on any failure.
Checks for every 3 <= n <= N, 1 <= m < n/2: S_k > 0 for 1 <= k < n-m, S_{n-m} = 0, alpha_{n-m} = -w_n,
alpha changes sign at most once and from + to -, alpha_1 > 0 (Simmons); for n = 2m all alpha_i = 0.
Also the numbers printed in the paper: Bin(7,3/7) partial sums and Figure 1 (Bin(10,3/10))."""
from math import comb
import sys

def alphas(n: int, m: int) -> list[int]:
    w = [comb(n, j) * m**j * (n - m)**(n - j) for j in range(n + 1)]
    out = []
    for i in range(1, n - m + 1):
        lo = sum(w[j] for j in range(0, max(m - i + 1, 0)))
        hi = sum(w[j] for j in range(m + i, n + 1))
        out.append(lo - hi)
    return out

N = int(sys.argv[1]) if len(sys.argv) > 1 else 150
count = 0
for n in range(3, N + 1):
    for m in range(1, n // 2 + 1):
        a = alphas(n, m)
        if 2 * m == n:
            assert all(x == 0 for x in a[:m]), (n, m)
            continue
        q = n - m
        assert a[0] > 0, ("Simmons", n, m)
        assert a[-1] == -(m**n), ("alpha_q", n, m)
        S, s = [], 0
        for x in a:
            s += x; S.append(s)
        assert S[-1] == 0 and all(v > 0 for v in S[:-1]), ("partial sums", n, m)
        sg = [x > 0 for x in a if x != 0]
        assert all(not (not sg[i] and sg[i + 1]) for i in range(len(sg) - 1)), ("sign pattern", n, m)
        count += 1
print(f"PASS: {count} pairs (n, m) with 3 <= n <= {N}, n > 2m")

a = alphas(7, 3)
assert a[:3] == [10249, -1847, -6215]
assert [sum(a[:k]) for k in (1, 2, 3)] == [10249, 8402, 2187]
fig_alpha = [0.0323935, -0.00095999, -0.0191015, -0.0105921, -0.00159039, -0.000143686, -0.0000059]
fig_S = [0.0323935, 0.0314335, 0.0123321, 0.00173998, 0.000149591, 0.0000059, 0]
a = alphas(10, 3); D = 10**10
for x, f in zip(a, fig_alpha):
    assert abs(x / D - f) < 1e-7, (x / D, f)
for k, f in enumerate(fig_S, 1):
    assert abs(sum(a[:k]) / D - f) < 1e-7, (k, f)
print("PASS: Bin(7,3/7) values and Figure 1 data match the paper")
