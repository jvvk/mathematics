"""Independent recheck for the note (shares no code with ../count.py).

1. For n <= 5, count cycles of length 2^n - 2 in B(n) as Eulerian circuits of B(n-1) with two edges
   removed, by backtracking over EDGES (count.py backtracks over vertices of B(n)), for every pair of edges.
2. For n <= 11, count spanning in-arborescences of B(n-1) minus each balanced pair with an exact
   Fraction elimination written here, rooted at the last vertex (count.py uses Bareiss, root 0).
3. Check the closed forms of Theorem 1 and the n = 3 examples in Section 1.
"""
from fractions import Fraction
from itertools import combinations
import sys


def edges_of(m):
    N = 1 << m
    return [(u, (u << 1 | b) & (N - 1)) for u in range(N) for b in (0, 1)]


def circuits(edge_list):
    """Eulerian circuits counted as cyclic sequences of edges (start fixed at edge 0)."""
    if not edge_list:
        return 0
    out = {}
    for i, (u, v) in enumerate(edge_list):
        out.setdefault(u, []).append(i)
    used = [False] * len(edge_list)
    total = len(edge_list)

    def go(v, k):
        if k == total:
            return 1 if v == edge_list[0][0] else 0
        s = 0
        for i in out.get(v, []):
            if not used[i]:
                used[i] = True
                s += go(edge_list[i][1], k + 1)
                used[i] = False
        return s

    used[0] = True
    return go(edge_list[0][1], 1)


def direct(n):
    E = edges_of(n - 1)
    return sum(circuits([e for i, e in enumerate(E) if i not in pair]) for pair in combinations(range(len(E)), 2))


def arbs(N, E, root):
    L = [[Fraction(0)] * N for _ in range(N)]
    for u, v in E:
        if u != v:
            L[u][u] += 1
            L[u][v] -= 1
    M = [[L[i][j] for j in range(N) if j != root] for i in range(N) if i != root]
    d = Fraction(1)
    n = len(M)
    for c in range(n):
        piv = next((r for r in range(c, n) if M[r][c] != 0), None)
        if piv is None:
            return 0
        if piv != c:
            M[c], M[piv] = M[piv], M[c]
            d = -d
        d *= M[c][c]
        for r in range(c + 1, n):
            f = M[r][c] / M[c][c]
            for j in range(c, n):
                M[r][j] -= f * M[c][j]
    return int(d)


def cases(n):
    m = n - 1
    N = 1 << m
    E = edges_of(m)
    alt = [int("".join("01"[(i + s) % 2] for i in range(m)), 2) for s in (0, 1)]
    loops = [e for e in E if e[0] == e[1]]
    two = [e for e in E if e[0] != e[1] and {e[0], e[1]} == set(alt)]
    a = arbs(N, [e for e in E if e not in loops], N - 1)
    b = arbs(N, [e for e in E if e not in two], N - 1) if len(two) == 2 else 0
    return a, b


def T(n):
    return Fraction((2 ** n - (-1) ** n) * 2 ** (2 ** (n - 1) - 2 * n + 2), 3)


def caseB(n):
    return Fraction((2 ** (n - 2) - (-1) ** n) * 2 ** (2 ** (n - 1) - 2 * n + 2), 3)


def main(nmax_direct=5, nmax=11):
    for n in range(2, nmax_direct + 1):
        d = direct(n)
        assert d == T(n), (n, d, T(n))
        print(f"n={n}: direct edge enumeration {d} = T(n)")
    for n in range(2, nmax + 1):
        a, b = cases(n)
        assert a == 2 ** (2 ** (n - 1) - n), (n, a)
        assert b == caseB(n), (n, b)
        assert a + b == T(n)
    print(f"tree counts for both cases match Theorem 1 for 2 <= n <= {nmax}")
    assert [T(n) for n in range(2, 7)] == [1, 3, 20, 2816, 88080384]
    assert [Fraction(2 ** n - (-1) ** n, 3) for n in range(1, 6)] == [1, 1, 3, 5, 11]
    # Section 1: the circles of length 6 with distinct 3-blocks, and those of length 8
    def circles(L, n=3):
        found = set()
        for x in range(1 << L):
            s = format(x, f"0{L}b")
            blocks = [(s + s)[i:i + n] for i in range(L)]
            if len(set(blocks)) == L:
                found.add(min(s[i:] + s[:i] for i in range(L)))
        return sorted(found)
    assert circles(6) == ["000111", "001011", "001101"], circles(6)
    assert circles(8) == ["00010111", "00011101"], circles(8)
    print("Section 1 examples confirmed")


if __name__ == "__main__":
    if len(sys.argv) > 1 and sys.argv[1] == "--mutants":
        # each mutant must make main() fail
        killed = 0
        for name, patch in [("T off by sign", lambda: globals().__setitem__("T", lambda n: Fraction((2 ** n + (-1) ** n) * 2 ** (2 ** (n - 1) - 2 * n + 2), 3))),
                            ("case B formula", lambda: globals().__setitem__("caseB", lambda n: Fraction((2 ** (n - 2) + (-1) ** n) * 2 ** (2 ** (n - 1) - 2 * n + 2), 3)))]:
            saved = {k: globals()[k] for k in ('T', 'caseB')}
            patch()
            try:
                main(4, 6)
                print("SURVIVED", name)
            except AssertionError:
                killed += 1
                print("killed", name)
            globals().update(saved)
        sys.exit(0 if killed == 2 else 1)
    main()
