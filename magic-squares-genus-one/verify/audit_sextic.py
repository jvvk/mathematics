"""Claude's independent re-implementation of the CENTRE_SEXTICS.md filters (Codex-originated), for audit.

Written from the mathematics, not from centre_sextic.py. Differences in method:
- forced values from leading coefficients kappa (z^-2 coefficients of h_i at a simple point; kappa_3 = kappa_1 +
  kappa_2, kappa_4 = kappa_1 - kappa_2, kappa_c = 0 at the non-full pair c), not from perpendicular vectors;
- group-law coincidences decided by grouplaw_exact.decide (Smith form + torsion search), not integer certificates;
- pencil obstruction: relation coefficients from a nullspace, squareness by factorisation over Q.
Compares the verdict on every input configuration with Codex's certificate file.
"""

from __future__ import annotations

import itertools
import json
import sys
from collections import Counter
from fractions import Fraction
from pathlib import Path

import sympy as S

from grouplaw_exact import decide

HERE = Path(__file__).parent
HV = [(1, 0), (0, 1), (1, 1), (1, -1)]
X = S.Symbol("X")


def rows_of(cfg):
    return [[col[1 + i] for col in cfg] for i in range(4)]


def kappa(col, mu):
    """Leading z^(-2 mu) coefficient vector (up to scale) of (h_1..h_4), or None if not forced.

    Lemma 1: at least three pairs are full (|eps| = mu); if one pair c is not, kappa_c = 0 fixes kappa.
    """
    low = [c for c in range(4) if abs(col[c]) < mu]
    if not low:
        return None
    (c,) = low
    k1, k2 = -HV[c][1], HV[c][0]          # H_c . (k1, k2) = 0
    return [Fraction(h[0] * k1 + h[1] * k2) for h in HV], c


def mono_div(u, rows):
    return [sum(u[k] * rows[k][p] for k in range(4)) for p in range(len(rows[0]))]


def deg(d):
    return sum(t for t in d if t > 0)


def forced(u, cfg):
    """{point: (value^2 of phi^u, forced multiplicity)} where phi^u is a unit and its value is forced.

    phi_k ~ a_k z^{e_k}; for |e_k| = mu, h_k ~ a_k^{-2 s_k} z^{-2 mu} (s_k = sign e_k), so kappa_k is proportional
    to a_k^{-2 s_k}. Value^2 of phi^u = prod a_k^{2 u_k} = prod kappa_k^{-u_k s_k} (scale cancels as phi^u is a
    unit). Multiplicity >= 2 (mu - |eps_c|) (CENTRE_SEXTICS.md (2)).
    """
    out = {}
    for p, col in enumerate(cfg):
        mu, e = col[0], col[1:]
        if sum(u[k] * e[k] for k in range(4)) != 0:
            continue
        kc = kappa(e, mu)
        if kc is None:
            continue
        kap, c = kc
        support = [k for k in range(4) if u[k]]
        if any(abs(e[k]) != mu for k in support):
            continue
        val = Fraction(1)
        for k in support:
            val *= kap[k] ** (-u[k] * (1 if e[k] > 0 else -1))
        out[p] = (val, 2 * (mu - abs(e[c])))
    return out


def ram_and_relations(cfg):
    rows = rows_of(cfg)
    extra = []
    for i, j in itertools.combinations(range(4), 2):
        for sj in (1, -1):
            u = [0] * 4
            u[i], u[j] = 1, sj
            d = mono_div(u, rows)
            fv = forced(u, cfg)
            dl = deg(d)
            if dl == 0:
                if len({v for v, _ in fv.values()}) > 1:
                    return "constant monomial, two values"
                continue
            if any(r > dl for _, r in fv.values()):
                return "fibre multiplicity"
            ram = sum(abs(t) - 1 for t in d if t) + sum(r - 1 for _, r in fv.values())
            if ram > 2 * dl:
                return "RH"
            for z in {v for v, _ in fv.values()}:
                if sum(r for v, r in fv.values() if v == z) > 2 * dl:
                    return "two fibres"
            for p, (_, r) in fv.items():
                if r == dl:
                    rel = [max(t, 0) for t in d]
                    rel[p] -= dl
                    extra.append(rel)
    A = [r[1:] for r in rows + extra if any(r)]
    if decide(A, len(cfg)) == "none":
        return "group law"
    return None


def pencil(cfg):
    rows = rows_of(cfg)
    for C in range(4):
        if deg(rows[C]) != 3:
            continue
        for A_, B_ in itertools.combinations([k for k in range(4) if k != C], 2):
            for sa, sb, sc in itertools.product((1, -1), repeat=3):
                uf = [0] * 4
                uf[A_], uf[C] = sa, -sc
                ug = [0] * 4
                ug[B_], ug[C] = sb, -sc
                df, dg = mono_div(uf, rows), mono_div(ug, rows)
                if sorted(t for t in df if t) != [-2, 2] or sorted(
                    t for t in dg if t
                ) != [-2, 2]:
                    continue
                R, P, Q = df.index(-2), df.index(2), dg.index(2)
                if dg.index(-2) != R or P == Q:
                    continue
                ff = {k: v for k, (v, _) in forced(uf, cfg).items()}
                fg = {k: v for k, (v, _) in forced(ug, cfg).items()}
                F, G = ff.get(Q), fg.get(P)
                for T in range(len(cfg)):
                    if T in (R, P, Q) or T not in ff or T not in fg:
                        continue
                    if F is None and G is not None and fg[T] == G:
                        F = ff[T] / 4
                    if G is None and F is not None and ff[T] == F:
                        G = fg[T] / 4
                if F is None or G is None:
                    continue
                M = S.Matrix(
                    [[HV[A_][0], HV[B_][0], HV[C][0]], [HV[A_][1], HV[B_][1], HV[C][1]]]
                )
                (ns,) = M.nullspace()
                a, b, c = ns
                F_, G_ = (
                    S.Rational(F.numerator, F.denominator),
                    S.Rational(G.numerator, G.denominator),
                )
                den = a * F_ * X**2 + b * G_ * (X - 1) ** 2 + c
                if S.expand(den) == 0:
                    continue
                Rx = S.cancel(-(a / (F_ * X**2) + b / (G_ * (X - 1) ** 2) + c) / den)
                n_, d_ = S.fraction(Rx)
                odd = any(
                    m % 2 for pol in (n_, d_) for _, m in S.factor_list(pol, X)[1]
                )
                if odd:
                    return f"pencil C={C} A={A_} B={B_} R={Rx}"
    return None


def three_affine(cfg):
    rows = rows_of(cfg)
    if any(deg(r) != 3 for r in rows):
        return None
    for s in itertools.product((1, -1), repeat=4):
        ds = [
            [s[j] * rows[j][p] - s[0] * rows[0][p] for p in range(len(cfg))]
            for j in (1, 2, 3)
        ]
        if all(sorted(t for t in d if t) == [-2, 2] for d in ds):
            if (
                len({d.index(-2) for d in ds}) == 1
                and len({d.index(2) for d in ds}) == 3
            ):
                return "three affine"
    return None


def monomial85(cfg):
    rows = rows_of(cfg)
    for s in itertools.product((1, -1), repeat=4):
        if any(mono_div([s[0], -s[1], -s[2], s[3]], rows)):
            continue
        if (
            deg(mono_div([s[0], -s[1], 0, 0], rows)) == 2
        ):  # Section 5 uses only deg f = 2
            return "monomial relation, deg f = 2"
    return None


def verdict(cfg):
    return (
        ram_and_relations(cfg)
        or pencil(cfg)
        or three_affine(cfg)
        or monomial85(cfg)
        or "SURVIVES"
    )


def main():
    src = sys.argv[1] if len(sys.argv) > 1 else "m6_distinct_survivors.json"
    data = json.loads((HERE / src).read_text())
    mine = [verdict(d["cfg"]) for d in data]
    print(Counter(v.split(" C=")[0] for v in mine))
    cert = HERE / "m6_centre_sextic_certificates.json"
    if src == "m6_distinct_survivors.json":
        if len(data) != 202:
            sys.exit(f"FAIL: expected 202 input tables, got {len(data)}")
        if not cert.exists():
            sys.exit("FAIL: m6_centre_sextic_certificates.json missing; run centre_sextic.py 6 first")
    if src == "m6_distinct_survivors.json" and cert.exists():
        theirs = {
            e["index"]: e["reason"] for e in json.loads(cert.read_text())["exclusions"]
        }
        cross = Counter(
            (theirs.get(k, "SURVIVES"), mine[k].split(" C=")[0])
            for k in range(len(data))
        )
        for kv, n in sorted(cross.items()):
            print(n, kv)
        same = {("all-pair RH", "RH"), ("forced coincidence", "group law"),
                ("degree-two pencil square obstruction", "pencil"),
                ("four-function monomial relation", "monomial relation, deg f = 2"),
                ("three affine functions", "three affine")}
        bad = {kv: n for kv, n in cross.items() if kv not in same}
        if bad:
            sys.exit(f"FAIL: implementations disagree: {bad}")
    if any(v == "SURVIVES" for v in mine) and src == "m6_distinct_survivors.json":
        sys.exit("FAIL: a degree-6 table survives")


if __name__ == "__main__":
    main()
