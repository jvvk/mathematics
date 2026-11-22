"""Claude's independent re-implementation of Codex's jet-propagation exclusions (SEPTIC_JETS.md).

At a simple point P with non-full pair c, the three unit monomials g = phi_i^{s_i} phi_j^{-s_j} (i, j != c) satisfy
ord_P(g - g(P)) >= 3 for all of them iff h_c(P) = 0 (jet lemma). Seed: a degree-3 such f with Z_f - 3P in the
integer span of known principal rows (eps rows; Z_u - 2Q for degree-2 monomials u with a forced double point Q)
forces its fibre to be 3P, hence h_c(P) = 0. Then every degree-3 unit monomial at P has fibre 3P (add Z_g - 3P), and
a degree-2 one is impossible (order 3 > degree 2). Finally grouplaw_exact.decide on all rows. Lattice membership by
Smith normal form (written here, not imported from Codex's code).
"""

from __future__ import annotations

import itertools
import json
import sys
from collections import Counter
from pathlib import Path

import sympy as S
from audit_sextic import deg, forced, mono_div, rows_of
from grouplaw_exact import decide
from sympy.matrices.normalforms import smith_normal_decomp

HERE = Path(__file__).parent


def in_span(rows, target):
    M = S.Matrix(rows)
    D, U, V = smith_normal_decomp(M, domain=S.ZZ)  # D = U M V
    tV = S.Matrix([target]) * V
    r = sum(1 for k in range(min(D.shape)) if D[k, k] != 0)
    if any(tV[k] != 0 for k in range(r, M.cols)):
        return False
    return all(tV[k] % D[k, k] == 0 for k in range(r))


def base_rows(cfg):
    rows = [list(r) for r in rows_of(cfg)]
    out = [r for r in rows if any(r)]
    for u in itertools.product((-1, 0, 1), repeat=4):
        d = mono_div(list(u), rows)
        if deg(d) != 2:
            continue
        for p, (_, r) in forced(list(u), cfg).items():
            if r == 2:
                rel = [max(t, 0) for t in d]
                rel[p] -= 2
                out.append(rel)
    return out


def unit_monomials(cfg, p):
    e = cfg[p][1:]
    c = [k for k in range(4) if e[k] == 0]
    if len(c) != 1:
        return []
    c = c[0]
    out = []
    for i, j in itertools.combinations([k for k in range(4) if k != c], 2):
        u = [0] * 4
        u[i], u[j] = (1 if e[i] > 0 else -1), -(1 if e[j] > 0 else -1)
        out.append(u)
    return out


def verdict(cfg):
    rows = rows_of(cfg)
    base = base_rows(cfg)
    n = len(cfg)
    extra = []
    triple_points = []
    for p in range(n):
        if cfg[p][0] != 1:
            continue
        mons = unit_monomials(cfg, p)
        for u in mons:
            d = mono_div(u, rows)
            if deg(d) != 3:
                continue
            t = [max(x, 0) for x in d]
            t[p] -= 3
            if in_span(base, t):
                triple_points.append(p)
                break
    for p in triple_points:
        for u in unit_monomials(cfg, p):
            d = mono_div(u, rows)
            if deg(d) == 2:
                return "degree-2 monomial with a triple point"
            if deg(d) == 3:
                t = [max(x, 0) for x in d]
                t[p] -= 3
                extra.append(t)
    if not triple_points:
        return "no seed"
    A = [r[1:] for r in base + extra]
    return "EXCLUDED (group law)" if decide(A, n) == "none" else "seed, but survives"


def main():
    data = json.loads((HERE / sys.argv[1]).read_text())
    res = [verdict(d["cfg"]) for d in data]
    print(Counter(res))
    exc = [
        k
        for k, v in enumerate(res)
        if v.startswith("EXCLUDED") or v.startswith("degree-2")
    ]
    print("excluded indices:", exc)
    (HERE / f"jets_claude_{Path(sys.argv[1]).stem}.json").write_text(
        json.dumps(res, indent=1) + "\n"
    )


if __name__ == "__main__":
    main()
