"""Export and check torsion-case certificates for group-law exclusions with no integer P_j - P_k certificate.

For a relation matrix A (rows = principal divisors on P_1..P_{n-1}, P_0 = origin), the Smith decomposition D = U A V
gives all solutions q = V w with w_k in E[d_k] (k < rank, d_k = D[k,k]) and w_k free (k >= rank). Writing
q_j = F_j(w_free) + T_j(t), the table is excluded iff for EVERY torsion choice t some point is forced to the origin
(F_j = 0 and T_j(t) = 0) or two points coincide (F_j = F_k and T_j(t) = T_k(t)). A certificate lists D, V, and for
each torsion choice t (in prod (Z/d_k)^2) the forced coincidence. The checker recomputes D = U A V by matrix
multiplication, checks unimodularity, enumerates the torsion choices itself, and checks each listed coincidence.
"""

from __future__ import annotations

import itertools
import json
import sys
from fractions import Fraction
from pathlib import Path

import sympy as S
from sympy.matrices.normalforms import smith_normal_decomp

from enum_indep import enumerate_all
from grouplaw_exact import decide
from jets_claude import in_span

HERE = Path(__file__).parent


def parts(V, D, n):
    r = sum(1 for k in range(min(D.shape)) if D[k, k] != 0)
    d = [abs(int(D[k, k])) for k in range(r)]
    tors = [k for k in range(r) if d[k] > 1]
    free = list(range(r, n - 1))
    F = [tuple(int(V[j, l]) for l in free) for j in range(n - 1)]
    return d, tors, F


def torsion_points(V, d, tors, t, n):
    T = []
    for j in range(n - 1):
        v = [Fraction(0), Fraction(0)]
        for k, tk in zip(tors, t):
            v[0] += int(V[j, k]) * Fraction(tk[0], d[k])
            v[1] += int(V[j, k]) * Fraction(tk[1], d[k])
        T.append(tuple(x - (x.numerator // x.denominator) for x in v))
    return T


def coincidence(F, T, n):
    for j in range(n - 1):
        if all(c == 0 for c in F[j]) and T[j] == (0, 0):
            return [0, j + 1]  # P_{j+1} forced to the origin P_0
    for j, k in itertools.combinations(range(n - 1), 2):
        if F[j] == F[k] and T[j] == T[k]:
            return [j + 1, k + 1]
    return None


def certificate(A, n):
    M = S.Matrix(A)
    D, U, V = smith_normal_decomp(M, domain=S.ZZ)
    d, tors, F = parts(V, D, n)
    cases = []
    for t in itertools.product(
        *[list(itertools.product(range(d[k]), repeat=2)) for k in tors]
    ):
        c = coincidence(F, torsion_points(V, d, tors, t, n), n)
        assert c is not None
        cases.append({"torsion": [list(x) for x in t], "coincide": c})
    return {"A": A, "U": U.tolist(), "D": D.tolist(), "V": V.tolist(), "cases": cases}


def check(cert, n):
    A, U, D, V = (S.Matrix(cert[k]) for k in ("A", "U", "D", "V"))
    assert U * A * V == D, "D != U A V"
    assert abs(U.det()) == 1 and abs(V.det()) == 1, "not unimodular"
    for i in range(D.rows):
        for j in range(D.cols):
            assert i == j or D[i, j] == 0, "D not diagonal"
    d, tors, F = parts(V, D, n)
    expected = list(
        itertools.product(
            *[list(itertools.product(range(d[k]), repeat=2)) for k in tors]
        )
    )
    got = [tuple(tuple(x) for x in c["torsion"]) for c in cert["cases"]]
    assert sorted(got) == sorted(expected), "torsion cases incomplete"
    for c in cert["cases"]:
        T = torsion_points(V, d, tors, [tuple(x) for x in c["torsion"]], n)
        j, k = c["coincide"]
        if j == 0:
            assert all(x == 0 for x in F[k - 1]) and T[k - 1] == (0, 0)
        else:
            assert F[j - 1] == F[k - 1] and T[j - 1] == T[k - 1]
    return True


def main():
    m = int(sys.argv[1]) if len(sys.argv) > 1 else 6
    out = []
    for tab in sorted(enumerate_all(m)):
        cfg = [list(c) for c in tab]
        n = len(cfg)
        rows = [[c[1 + i] for c in cfg] for i in range(4)]
        R = [r for r in rows if any(r)]
        A = [r[1:] for r in R]
        if decide(A, n) != "none":
            continue
        if any(
            in_span(R, [int(p == j) - int(p == k) for p in range(n)])
            for j, k in itertools.combinations(range(n), 2)
        ):
            continue
        cert = certificate(A, n)
        assert check(cert, n)
        out.append({"cfg": cfg, "certificate": cert})
    (HERE / f"m{m}_torsion_certificates.json").write_text(
        json.dumps(out, indent=1, default=int) + "\n"
    )
    print(f"m={m}: {len(out)} torsion-case certificates exported and checked")
    if m == 6 and len(out) != 19:
        sys.exit(f"FAIL: expected 19, got {len(out)}")


if __name__ == "__main__":
    main()
