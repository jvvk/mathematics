"""Augment the group law with total-ramification relations from Lemma 2.

For f in {s, d} of a relation (A,B), div f = e_A +- e_B, deg f = delta. Every fibre of f sums to
Z_f = sum_P max(div_P, 0) P. If Lemma 2 forces ord_P(f - f(P)) >= r with r >= delta at a point P (where f is a unit),
then r == delta (else excluded) and delta * P = Z_f. Add these relations to the eps-relations and reclassify.
"""
import json
import sys
from collections import Counter, defaultdict
from pathlib import Path

import sympy as S

from mconfigs import classify
from rh_filter import RELS

HERE = Path(__file__).parent


def extra_relations(cfg):
    pts = [(c[0], c[1:]) for c in cfg]
    rels = []
    for A, B, C, kind in RELS:
        for P, (mu, e) in enumerate(pts):
            M = max(abs(e[A]), abs(e[B]))
            if abs(e[C]) < M:
                sign = 1 if e[A] == -e[B] else -1
                div = [q[A] + sign * q[B] for _, q in pts]
                delta = sum(x for x in div if x > 0)
                r = 2 * (M - abs(e[C]))
                if delta == 0:
                    continue
                if r > delta:
                    return None
                if r == delta:
                    row = [max(x, 0) for x in div]
                    row[P] -= delta
                    rels.append(row)
    return rels


def classify_aug(cfg, extra):
    n = len(cfg)
    rows = [[col[1 + i] for col in cfg] for i in range(4)] + extra
    fake = []
    # reuse classify by building a pseudo-configuration with more 'pair' rows: classify reads 4 rows; pass rows directly
    from mconfigs import S as _S  # noqa
    A = [r[1:] for r in rows if any(r[1:]) or any(r)]
    A = [r for r in A if any(r)]
    return classify_rows(A, n)


def classify_rows(A, n):
    import itertools
    from math import gcd
    from sympy.matrices.normalforms import smith_normal_form
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
    K = S.Matrix.hstack(*M.nullspace())
    K = K * S.ilcm(*[x.q for x in K if x != 0] or [1])
    rws = [tuple(K.row(j)) for j in range(n - 1)]
    if any(all(t == 0 for t in r) for r in rws) or len(set(rws)) < n - 1:
        return f"family d={n - 1 - rk} (coincidence)"
    return f"family d={n - 1 - rk}"


def main():
    m = sys.argv[1]
    data = json.loads((HERE / f"m{m}_rh_survivors.json").read_text())
    out, stats = [], Counter()
    for d in data:
        ex = extra_relations(d["cfg"])
        if ex is None:
            stats["excluded (r > deg)"] += 1
            continue
        # translate: rows are over all points; first point is O, drop its column
        A = [r[1:] for r in ([[c[1 + i] for c in d["cfg"]] for i in range(4)] + ex) if any(r[1:])]
        cl = classify_rows(A, len(d["cfg"]))
        stats[(tuple(d["mu"]), cl)] += 1
        if cl != "none":
            d2 = dict(d); d2["class_aug"] = cl; d2["extra"] = ex
            out.append(d2)
    for k, v in sorted(stats.items(), key=str):
        print(k, v)
    print("remaining:", len(out))
    (HERE / f"m{m}_aug_survivors.json").write_text(json.dumps(out))


if __name__ == "__main__":
    main()
