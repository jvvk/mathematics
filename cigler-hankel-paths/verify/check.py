"""MO 456683 (Cigler): D_{k,n}(x,c) = det(a_{i+j,k})_{0<=i,j<n} equals det H_{k,n}(x), independent of c;
and d_{k,n} d_{k,n-2k-2} - x^2 d_{k,n-1} d_{k,n-2k-1} = (1-x^2) d_{k,n-k-1}^2 for n >= 2k+2.
Checked at integer points (x, c) with exact Bareiss determinants."""
import random


def det(M: list[list[int]]) -> int:
    n = len(M)
    if n == 0:
        return 1
    A = [r[:] for r in M]
    sign, prev = 1, 1
    for i in range(n - 1):
        if A[i][i] == 0:
            sw = next((r for r in range(i + 1, n) if A[r][i] != 0), None)
            if sw is None:
                return 0
            A[i], A[sw] = A[sw], A[i]
            sign = -sign
        for r in range(i + 1, n):
            for s in range(i + 1, n):
                A[r][s] = (A[r][s] * A[i][i] - A[r][i] * A[i][s]) // prev
        prev = A[i][i]
    return sign * A[n - 1][n - 1]


def a_table(N: int, x: int, c: int) -> list[list[int]]:
    a = [[0] * (N + 3) for _ in range(N + 1)]
    a[0][0] = 1
    for n in range(1, N + 1):
        for k in range(0, n + 1):
            s = c + x if k == 0 else c
            a[n][k] = (a[n - 1][k - 1] if k else 0) + s * a[n - 1][k] + a[n - 1][k + 1]
    return a


def D(k: int, n: int, a) -> int:
    return det([[a[i + j][k] for j in range(n)] for i in range(n)])


def H(k: int, n: int, x: int) -> int:
    M = [[0] * n for _ in range(n)]
    for l in range(n):
        for m in range(k + 1):
            i, j = k - m + l, m + l
            if i < n and j < n:
                M[i][j] = 1
        for i2 in range(1, n):
            j = k + i2 + l
            if j < n:
                M[l][j] = x**i2
    return det(M)


random.seed(1)
NMAX = 22
bad = 0
for trial in range(6):
    x, c1, c2 = random.randint(-7, 7), random.randint(-9, 9), random.randint(-9, 9)
    a1, a2 = a_table(2 * NMAX, x, c1), a_table(2 * NMAX, x, c2)
    for k in range(1, 6):
        for n in range(NMAX):
            d1, d2, h = D(k, n, a1), D(k, n, a2), H(k, n, x)
            if not (d1 == d2 == h):
                bad += 1
                print("MISMATCH", dict(x=x, c1=c1, c2=c2, k=k, n=n, d1=d1, d2=d2, h=h))
        Hs = [H(k, n, x) for n in range(NMAX)]
        for n in range(2 * k + 2, NMAX):
            if Hs[n] * Hs[n - 2 * k - 2] - x * x * Hs[n - 1] * Hs[n - 2 * k - 1] != (1 - x * x) * Hs[n - k - 1] ** 2:
                bad += 1
                print("REC FAIL", x, k, n)
print("checks done, failures:", bad, f"(k=1..5, n<{NMAX}, 6 random (x,c1,c2))")
assert bad == 0, f"{bad} failures"
