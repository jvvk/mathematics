"""Centre-pair configurations for general m (generalises m5_configs.py).

A configuration: points P with multiplicities mu_P (sum m) and columns c_P = (eps_1P..eps_4P), |eps| <= mu_P,
at least three entries with |eps| = mu_P (Lemma 1). Rows: sum_P eps_iP = 0, sum_P |eps_iP| != 2 (k_i != 1).
Symmetries: permutations of points with equal mu, sign flip of each row. Group law (first point = O): relation
matrix A (nonzero rows) on q_1..q_{n-1}. Classify:
  torsion  : rank A = n-1; distinct nonzero solution exists in E[N] (N = gcd of maximal minors' lattice index)
  family(d): rank A = n-1-d < n-1; generic distinctness tested on the identity component (integer kernel basis)
  none     : no admissible points.
"""
from __future__ import annotations

import itertools
import json
import sys
from collections import Counter
from math import gcd
from pathlib import Path

import sympy as S
from sympy.matrices.normalforms import smith_normal_form


def partitions(n, maxpart=None):
    if n == 0:
        yield ()
        return
    for p in range(min(n, maxpart or n), 0, -1):
        for rest in partitions(n - p, p):
            yield (p,) + rest


def columns(mu):
    out = []
    for c in itertools.product(range(-mu, mu + 1), repeat=4):
        if sum(1 for t in c if abs(t) == mu) >= 3:
            out.append(c)
    return out


def configs(mu_part):
    n = len(mu_part)
    cols = {mu: columns(mu) for mu in set(mu_part)}
    res = set()
    cap_after = [sum(mu_part[j:]) for j in range(n + 1)]

    def rec(j, prev_idx, rows):
        if j == n:
            if all(sum(r) == 0 for r in rows) and all(sum(abs(t) for t in r) != 2 for r in rows):
                res.add(canon(mu_part, rows))
            return
        mu = mu_part[j]
        start = prev_idx if j > 0 and mu_part[j - 1] == mu else 0
        for idx in range(start, len(cols[mu])):
            c = cols[mu][idx]
            new = [r + [c[i]] for i, r in enumerate(rows)]
            if all(abs(sum(r)) <= cap_after[j + 1] for r in new):
                rec(j + 1, idx, new)

    rec(0, 0, [[], [], [], []])
    return res


def canon(mu_part, rows):
    best = None
    n = len(mu_part)
    for signs in itertools.product((1, -1), repeat=4):
        cols_ = sorted(zip(mu_part, *[[s * t for t in r] for s, r in zip(signs, rows)]), key=lambda x: (-x[0], x[1:]))
        key = tuple(cols_)
        if best is None or key < best:
            best = key
    return best


def classify(cfg):
    n = len(cfg)
    rows = [[col[1 + i] for col in cfg] for i in range(4)]
    A = [r[1:] for r in rows if any(r)]
    if n == 1:
        return "none"
    M = S.Matrix(A) if A else S.zeros(1, n - 1)
    rk = M.rank()
    if rk == n - 1:
        snf = smith_normal_form(M, domain=S.ZZ)
        N = 1
        for k in range(min(snf.shape)):
            if snf[k, k] != 0:
                N = N * abs(int(snf[k, k])) // gcd(N, abs(int(snf[k, k])))
        if N == 1:
            return "none"
        sols = [c for c in itertools.product(range(N), repeat=n - 1)
                if all(sum(a * x for a, x in zip(r, c)) % N == 0 for r in A)]
        for s1 in sols:
            for s2 in sols:
                pts = [(s1[j], s2[j]) for j in range(n - 1)]
                if all(p != (0, 0) for p in pts) and len(set(pts)) == n - 1:
                    return f"torsion N={N}"
        return "none"
    K = M.nullspace()
    # integer kernel basis rows: point j's coefficients
    Kmat = S.Matrix.hstack(*K)
    Kmat = Kmat * S.ilcm(*[x.q for x in Kmat if x != 0] or [1])
    rws = [tuple(Kmat.row(j)) for j in range(n - 1)]
    if any(all(t == 0 for t in r) for r in rws) or len(set(rws)) < n - 1:
        return f"family d={n - 1 - rk} (forced coincidence on identity component; check cosets)"
    return f"family d={n - 1 - rk}"


def main():
    m = int(sys.argv[1])
    out = []
    stats = Counter()
    for mu_part in partitions(m):
        for cfg in configs(mu_part):
            cl = classify(cfg)
            ks = tuple(sum(abs(col[1 + i]) for col in cfg) // 2 for i in range(4))
            stats[(mu_part, cl.split(" (")[0])] += 1
            if cl != "none":
                out.append({"mu": mu_part, "cfg": [list(c) for c in cfg], "k": ks, "class": cl})
    for k, v in sorted(stats.items(), key=str):
        print(k, v)
    print("non-excluded:", len(out))
    Path(__file__).with_name(f"m{m}_configs.json").write_text(json.dumps(out))


if __name__ == "__main__":
    main()
