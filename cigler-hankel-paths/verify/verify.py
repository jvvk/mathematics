"""Independent checks of each step of the proof for MO 456683 (exact arithmetic).

Step 1  a_{n,k}(b,c) = sum_j C(n,j) c^(n-j) a_{j,k}(b,0)   (binomial transform), so D_{k,n}(b,c) = D_{k,n}(b,0).
Step 2  a_{i+j,k} = sum_l a_{i,l} W_j(l -> k)  with (a_{i,l}) lower unitriangular, so D_{k,n} = det W_n.
Step 3  W_n = H_n U_n, U_{i,j} = ballot number B(j,i) (paths 0 -> i in j steps, +-1 steps, >= 0); det U_n = 1.
Negative controls: perturbing H by one entry, or using level weight c != 0 inside W, must break Step 3 (asserted).
"""

import random
from math import comb

import sympy as sp

b = sp.symbols("b")


def a_table(N: int, bb, cc):
    a = [[0] * (N + 3) for _ in range(N + 1)]
    a[0][0] = 1
    for n in range(1, N + 1):
        for k in range(n + 1):
            s = cc + bb if k == 0 else cc
            a[n][k] = sp.expand(
                (a[n - 1][k - 1] if k else 0) + s * a[n - 1][k] + a[n - 1][k + 1]
            )
    return a


def W(j: int, l: int, k: int, bb, cc=0):
    cur = {l: 1}
    for _ in range(j):
        nxt: dict = {}
        for h, v in cur.items():
            for h2, w in ((h + 1, 1), (h - 1, 1), (h, cc + bb if h == 0 else cc)):
                if h2 >= 0 and w != 0:
                    nxt[h2] = sp.expand(nxt.get(h2, 0) + v * w)
        cur = nxt
    return cur.get(k, 0)


def ballot(j: int, i: int) -> int:
    if i > j or (j - i) % 2:
        return 0
    return comb(j, (j - i) // 2) - comb(j, (j - i) // 2 - 1) if (j - i) // 2 >= 1 else 1


def Hent(k: int, l: int, s: int, bb):
    if s - l > k:
        return bb ** (s - l - k)
    if abs(s - l) <= k:
        return 1 if (l + s - k) % 2 == 0 and l + s >= k else 0
    return 0


c = sp.symbols("c")
N = 16
A_bc, A_b0 = a_table(N, b, c), a_table(N, b, 0)
assert all(
    sp.expand(
        A_bc[n][k] - sum(comb(n, j) * c ** (n - j) * A_b0[j][k] for j in range(n + 1))
    )
    == 0
    for n in range(N + 1)
    for k in range(n + 1)
)
print("Step 1 ok (n <= 16, symbolic b, c)")

for k in range(5):
    for i in range(8):
        for j in range(8):
            assert (
                sp.expand(
                    A_bc[i + j][k]
                    - sum(A_bc[i][l] * W(j, l, k, b, c) for l in range(i + 1))
                )
                == 0
            )
assert all(A_bc[i][i] == 1 for i in range(N))
print("Step 2 ok (k <= 4, i, j < 8, symbolic b, c)")

for k in range(6):
    n = 12
    for l in range(n):
        for j in range(n):
            lhs = W(j, l, k, b)
            rhs = sum(Hent(k, l, i, b) * ballot(j, i) for i in range(j + 1))
            assert sp.expand(lhs - rhs) == 0, (k, l, j)
print("Step 3 ok (k <= 5, n = 12, symbolic b)")

# mutants
random.seed(7)
caught = 0
for trial in range(20):
    k = random.randint(1, 4)
    l0, s0 = random.randint(0, 9), random.randint(0, 9)

    def Hmut(kk, l, s, bb):
        return Hent(kk, l, s, bb) + (1 if (l, s) == (l0, s0) else 0)

    if any(
        sp.expand(
            W(j, l, k, b) - sum(Hmut(k, l, i, b) * ballot(j, i) for i in range(j + 1))
        )
        != 0
        for l in range(10)
        for j in range(10)
    ):
        caught += 1
nonzero_c = any(
    sp.expand(
        W(j, l, 2, b, 1) - sum(Hent(2, l, i, b) * ballot(j, i) for i in range(j + 1))
    )
    != 0
    for l in range(8)
    for j in range(8)
)
print(
    f"mutants: {caught}/20 single-entry H perturbations rejected; W with c=1 rejected: {nonzero_c}"
)
assert caught == 20 and nonzero_c, "a perturbation of H or c != 0 in W went undetected"
