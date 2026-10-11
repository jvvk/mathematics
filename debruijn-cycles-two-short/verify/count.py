"""Cycles of length 2^n - 2 in the binary de Bruijn graph B(n) (vertices = n-bit strings, v -> (2v + b) mod 2^n).

brute(n): direct DFS over simple cycles (n <= 4).
best(n): omitted edges of B(n-1) must be the two loops (case A) or the 2-cycle on the alternating vertices (case B);
each case is #arborescences of B(n-1) minus those edges (BEST: all out-degree factorials are 1).
"""
from fractions import Fraction
import sys


def brute(n: int) -> int:
    N, L = 1 << n, (1 << n) - 2
    count = 0
    for s in range(N):  # count each cycle once, from its smallest vertex
        stack = [(s, 1 << s, 1)]
        while stack:
            v, mask, ln = stack.pop()
            for b in (0, 1):
                w = (2 * v + b) % N
                if w == s and ln == L:
                    count += 1
                elif w > s and not mask >> w & 1 and ln < L:
                    stack.append((w, mask | 1 << w, ln + 1))
    return count


def det(M: list[list[int]]) -> int:
    """Exact determinant (Bareiss)."""
    M = [r[:] for r in M]
    n, sign, prev = len(M), 1, 1
    for k in range(n - 1):
        if M[k][k] == 0:
            for i in range(k + 1, n):
                if M[i][k]:
                    M[k], M[i] = M[i], M[k]; sign = -sign; break
            else:
                return 0
        for i in range(k + 1, n):
            for j in range(k + 1, n):
                M[i][j] = (M[i][j] * M[k][k] - M[i][k] * M[k][j]) // prev
        prev = M[k][k]
    return sign * M[-1][-1]


def arborescences(N: int, edges: list[tuple[int, int]], root: int = 0) -> int:
    """# spanning arborescences oriented towards root (out-degree Laplacian, delete root row/col)."""
    L = [[0] * N for _ in range(N)]
    for u, v in edges:
        if u != v:
            L[u][u] += 1; L[u][v] -= 1
    keep = [i for i in range(N) if i != root]
    return det([[L[i][j] for j in keep] for i in keep])


def best(n: int) -> tuple[int, int]:
    m = n - 1
    N = 1 << m
    E = [(v, (2 * v + b) % N) for v in range(N) for b in (0, 1)]
    p = int("01" * m, 2) >> (m % 2) if m > 0 else 0
    p = sum(1 << i for i in range(0, m, 2))  # ...0101 (m bits)
    q = p ^ (N - 1)                           # ...1010
    caseA = [e for e in E if e[0] != e[1]]    # loops do not change arborescences anyway
    R = {(p, q), (q, p)}
    assert all(e in E for e in R)
    caseB = [e for e in E if e not in R]
    return arborescences(N, caseA), arborescences(N, caseB)


if __name__ == "__main__":
    for n in range(2, int(sys.argv[1]) + 1):
        a, b = best(n)
        kib = Fraction(2 ** (2 ** n - 2 * n) * (2 ** (n - 1) + (-1) ** n), 3)
        br = brute(n) if n <= 4 else None
        print(n, "A", a, "B", b, "total", a + b, "brute", br, "quoted formula", kib)


def closed_forms(n: int) -> tuple[int, Fraction, Fraction]:
    m = n - 1
    A = 2 ** (2 ** m - m - 1)
    B = Fraction(2 ** (2 ** m - 2 * m) * (2 ** (m - 1) + (-1) ** m), 3) if m >= 1 else Fraction(0)
    T = Fraction((2 ** n - (-1) ** n) * 2 ** (2 ** m - 2 * n + 2), 3)
    return A, B, T


def check(nmax: int) -> None:
    for n in range(2, nmax + 1):
        a, b = best(n)
        A, B, T = closed_forms(n)
        assert (a, b) == (A, B) and a + b == T, n
        if n <= 5:
            assert brute(n) == a + b, n
    print(f"closed forms A, B, T verified for 2 <= n <= {nmax} (brute force n <= 5)")
