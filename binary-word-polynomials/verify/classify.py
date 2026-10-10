"""Census of coincidences by proved mechanism, on reversal orbits.

Block-reversal lemma. Let G be an invertible symmetric 2x2 matrix over Q(t) with M_Y G symmetric for every block Y.
For words A, A', B, B' put x_A = M_A^T e1 and y_B = M_B e1. If G x_A = lam y_B' and G x_A' = (1/mu) y_B with
lam mu = 1, then P(A Y1..Ym B) = P(A' Ym..Y1 B').
  Proof: P = x_A^T V y_B with V = M_Y1..M_Ym; V^T = G^{-1} V_rev G, so P = (G^{-1} y_B)^T V_rev (G x_A).

Edges of the coincidence graph on reversal orbits:
  M1  v = complement of u, up to reversal (P_comp(w)(t) = (-1)^n P_w(1-t)).
  B   a block-reversal move u = A Y1..Ym B -> A' Ym..Y1 B' (m >= 2) with such a G.
All conditions on G = [[al, be], [be, ga]] are linear; they are solved modulo a large prime at several random t.
A fibre is explained when its orbits are connected by these edges.
Usage: python3 classify.py nmin nmax [--mut-...]; soundtest.py checks every accepted move and kills the mutants."""

import random
import sys

from exact import classes

PR = (1 << 61) - 1
random.seed(20261010)
PTS = [random.randrange(2, PR - 2) for _ in range(3)]
MUT = {
    m
    for m in ("--mut-nodet", "--mut-nolam", "--mut-noboundary", "--mut-noblocks")
    if m in sys.argv
}
comp = lambda w: w.translate(str.maketrans("01", "10"))


def mats(w: str, t: int) -> dict:
    """M[i, j] = transfer matrix of w[i:j] at t, as (m00, m01, m10, m11) mod PR."""
    n = len(w)
    M = {}
    for i in range(n + 1):
        m = (1, 0, 0, 1)
        M[i, i] = m
        for j in range(i, n):
            z = (t - int(w[j])) % PR  # m * [[z, -1], [1, 0]]
            m = ((m[0] * z + m[1]) % PR, -m[0] % PR, (m[2] * z + m[3]) % PR, -m[2] % PR)
            M[i, j + 1] = m
    return M


def kernel(rows: list) -> list:
    """Null space basis of rows (3 columns) mod PR."""
    rows = [list(r) for r in rows]
    piv = []
    r = 0
    for c in range(3):
        k = next((i for i in range(r, len(rows)) if rows[i][c]), None)
        if k is None:
            continue
        rows[r], rows[k] = rows[k], rows[r]
        inv = pow(rows[r][c], PR - 2, PR)
        rows[r] = [x * inv % PR for x in rows[r]]
        for i in range(len(rows)):
            if i != r and rows[i][c]:
                f = rows[i][c]
                rows[i] = [(x - f * y) % PR for x, y in zip(rows[i], rows[r])]
        piv.append(c)
        r += 1
    basis = []
    for fc in (c for c in range(3) if c not in piv):
        v = [0, 0, 0]
        v[fc] = 1
        for i, c in enumerate(piv):
            v[c] = -rows[i][fc] % PR
        basis.append(v)
    return basis


def block_row(m):  # M G symmetric:  m10 al + (m11 - m00) be - m01 ga = 0
    return (m[2], (m[3] - m[0]) % PR, -m[1] % PR)


def par_row(x, y):  # G x parallel to y
    return (x[0] * y[1] % PR, (x[1] * y[1] - x[0] * y[0]) % PR, -x[1] * y[0] % PR)


def ok_at(Mu, Mv, n, a, b, la, cuts, t, extra=()):
    """Does a valid G exist at the point t for this move?"""
    L = n - a - b
    rows = []
    for i in range(len(cuts) - 1):
        rows.append(block_row(Mu[a + cuts[i], a + cuts[i + 1]]))
    xA = Mu[0, a][0:2]
    yB = (Mu[n - b, n][0], Mu[n - b, n][2])
    xA2 = Mv[0, la][0:2]
    yB2 = (Mv[la + L, n][0], Mv[la + L, n][2])
    if "--mut-noblocks" in MUT:
        rows = []
    if "--mut-noboundary" not in MUT:
        rows += [par_row(xA, yB2), par_row(xA2, yB)]
    K = kernel(rows + list(extra))
    if not K:
        return False
    for _ in range(3):
        c = [random.randrange(1, PR) for _ in K]
        al, be, ga = (sum(ci * v[k] for ci, v in zip(c, K)) % PR for k in range(3))
        det = (al * ga - be * be) % PR
        if not det and "--mut-nodet" not in MUT:
            continue
        Gx = ((al * xA[0] + be * xA[1]) % PR, (be * xA[0] + ga * xA[1]) % PR)
        k = 0 if yB2[0] else 1
        lam = Gx[k] * pow(yB2[k], PR - 2, PR) % PR
        Gx2 = ((al * xA2[0] + be * xA2[1]) % PR, (be * xA2[0] + ga * xA2[1]) % PR)
        k = 0 if yB[0] else 1
        mu_inv = Gx2[k] * pow(yB[k], PR - 2, PR) % PR  # G x_A' = (1/mu) y_B
        if lam == mu_inv or "--mut-nolam" in MUT:
            return True
    return False


def moves(u: str, v: str):
    """Yield (a, b, la, blocks) for every block-reversal move u -> v (string conditions only)."""
    n = len(u)
    for a in range(n - 1):
        for b in range(n - a - 1):
            L = n - a - b
            X = u[a : a + L]
            for la in range(n - L + 1):
                Yr = v[la : la + L]
                # cut X into Y1..Ym (m >= 2) with Yr = Ym..Y1
                stack = [(0, [0])]
                while stack:
                    i, cuts = stack.pop()
                    if i == L:
                        if len(cuts) > 2:
                            yield a, b, la, cuts
                        continue
                    for j in range(i + 1, L + 1):
                        if X[i:j] == Yr[L - j : L - i]:
                            stack.append((j, cuts + [j]))


def b_edge(u: str, v: str, cache: dict) -> bool:
    n = len(u)
    for vv in {v, v[::-1]}:
        Ms = [
            (
                cache.setdefault((u, t), mats(u, t)),
                cache.setdefault((vv, t), mats(vv, t)),
            )
            for t in PTS
        ]
        for a, b, la, cuts in moves(u, vv):
            if all(ok_at(Mu, Mv, n, a, b, la, cuts, t) for (Mu, Mv), t in zip(Ms, PTS)):
                return True
    return False


def census(n: int):
    res = {"fibres": 0, "explained": 0, "M1": 0, "B": 0, "orbits": 0}
    left = []
    cache = {}
    for g in classes(n):
        res["fibres"] += 1
        res["orbits"] += len(g)
        parent = list(range(len(g)))

        def find(i):
            while parent[i] != i:
                i = parent[i]
            return i

        for i in range(len(g)):
            for j in range(i + 1, len(g)):
                u, v = g[i], g[j]
                if v in (comp(u), comp(u)[::-1]):
                    res["M1"] += 1
                    kind = True
                elif b_edge(u, v, cache):
                    res["B"] += 1
                    kind = True
                else:
                    kind = False
                if kind:
                    parent[find(i)] = find(j)
        if len({find(i) for i in range(len(g))}) == 1:
            res["explained"] += 1
        else:
            left.append(g)
    return res, left


if __name__ == "__main__":
    lo, hi = int(sys.argv[1]), int(sys.argv[2])
    for n in range(lo, hi + 1):
        res, left = census(n)
        print(n, res, "unexplained fibres", len(left), left[:3], flush=True)
