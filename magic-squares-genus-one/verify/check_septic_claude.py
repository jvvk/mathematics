"""Claude's independent check of Codex's degree-7 certificates (CENTRE_SEPTICS.md).

Rebuilds every ingredient from the configuration with audit_sextic.forced (Claude's kappa-based forced values):
- residual fibre: monomial divisor and degree 3; P a forced double point of f; every relation row is an eps row or a
  forced-full-fibre row (Z_g - delta P for a monomial g with forced multiplicity = deg g), up to sign; the integer
  combination equals Z_f - 2P - Q; Q is a zero/pole of f, or a forced double point of f with the same value^2
  (Q != P);
- packing: the listed points are forced for f with that value^2 and those multiplicities, and no split into two
  bins of capacity deg f exists (brute force);
- tame reciprocity: w_P = T eps_P vanishes at all-full columns and at the non-full entry, and the product of
  prod_{i != c} kappa_i^(-s_i w_i) over points is -1, recomputed from Claude's kappa.
"""

from __future__ import annotations

import itertools
import json
import sys
from fractions import Fraction
from pathlib import Path

from audit_sextic import deg, forced, kappa, mono_div, rows_of

HERE = Path(__file__).parent


def legit_rows(cfg):
    rows = rows_of(cfg)
    out = {tuple(r) for r in rows}
    for u in itertools.product((-1, 0, 1), repeat=4):
        if sum(map(abs, u)) == 0:
            continue
        d = mono_div(list(u), rows)
        dl = deg(d)
        if dl == 0:
            continue
        for p, (_, r) in forced(list(u), cfg).items():
            if r == dl:
                rel = [max(t, 0) for t in d]
                rel[p] -= dl
                out.add(tuple(rel))
    return out | {tuple(-t for t in r) for r in out}


def check_residual(cfg, c):
    rows = rows_of(cfg)
    u = c["monomial"]
    d = mono_div(u, rows)
    assert d == c["divisor"] and deg(d) == 3
    fv = forced(u, cfg)
    P, Q = c["double_point"], c["residual_point"]
    assert P in fv and fv[P][1] >= 2
    legit = legit_rows(cfg)
    assert all(tuple(r) in legit for r in c["relation_rows"]), (
        "unjustified relation row"
    )
    comb = [
        sum(a * r[p] for a, r in zip(c["coefficients"], c["relation_rows"]))
        for p in range(len(cfg))
    ]
    target = [max(t, 0) for t in d]
    target[P] -= 2
    target[Q] -= 1
    assert comb == target, (comb, target)
    if d[Q] != 0:
        return "zero or pole"
    # Q forced for f: if f(Q)^2 != f(P)^2, Q is not in the fibre over f(P); if equal, the fibre contains 2P + 2Q
    assert Q != P and Q in fv, "no contradiction at Q"
    return "same value: fibre >= 2P+2Q" if fv[Q][0] == fv[P][0] else "Q forced with a different value"


def check_packing(cfg, c):
    u = c["monomial"]
    d = mono_div(u, rows_of(cfg))
    dl = deg(d)
    assert d == c["divisor"] and dl == c["degree"]
    fv = forced(u, cfg)
    z = Fraction(c["value_squared"])
    w = []
    for p, r in c["points"]:
        assert p in fv and fv[p][0] == z and fv[p][1] >= r
        w.append(r)
    for split in itertools.product((0, 1), repeat=len(w)):
        if all(sum(x for x, s in zip(w, split) if s == b) <= dl for b in (0, 1)):
            raise AssertionError("packing feasible")
    return "infeasible"


def check_reciprocity(cfg, c):
    T = [[0] * 4 for _ in range(4)]
    for (i, j), a in zip(c["pair_order"], c["skew_coefficients"]):
        T[i][j], T[j][i] = a, -a
    prod = Fraction(1)
    for col in cfg:
        mu, e = col[0], col[1:]
        w = [sum(T[i][j] * e[j] for j in range(4)) for i in range(4)]
        kc = kappa(e, mu)
        if kc is None:
            assert not any(w), "nonzero exponent at an all-full point"
            continue
        kap, cc = kc
        assert w[cc] == 0
        for i in range(4):
            if i != cc and w[i]:
                s = 1 if e[i] > 0 else -1
                prod *= kap[i] ** (-s * w[i])
    assert prod == -1, prod
    return "product -1"


def main():
    data = json.loads((HERE / "m7_survivors.json").read_text())
    cert = json.loads((HERE / sys.argv[1]).read_text())
    from collections import Counter

    out = Counter()
    for e in cert["exclusions"]:
        cfg = data[e["index"]]["cfg"]
        fn = {
            "residual fibre": check_residual,
            "two-fibre packing": check_packing,
            "tame reciprocity": check_reciprocity,
        }[e["reason"]]
        out[(e["reason"], fn(cfg, e["certificate"]))] += 1
    print(dict(out), "total", sum(out.values()))
    import hashlib
    src = HERE / "m7_survivors.json"
    if hashlib.sha256(src.read_bytes()).hexdigest() != cert["source_sha256"]:
        sys.exit("FAIL: certificate source hash does not match m7_survivors.json")
    idx = [e["index"] for e in cert["exclusions"]]
    if not idx or any(not (0 <= k < len(data)) for k in idx):
        sys.exit("FAIL: empty or out-of-range certificate indices")
    if len(idx) != len(set(idx)):
        sys.exit("FAIL: duplicate certificate indices")
    surv = json.loads((HERE / "m7_fibre_reciprocity_survivors.json").read_text())
    keyset = {json.dumps(d["cfg"]) for d in surv}
    excl = {json.dumps(data[k]["cfg"]) for k in idx}
    allc = {json.dumps(d["cfg"]) for d in data}
    if keyset & excl or keyset | excl != allc or len(idx) + len(surv) != len(data):
        sys.exit("FAIL: exclusions and survivors do not partition the input")
    print("hash, uniqueness and coverage: OK")


if __name__ == "__main__":
    main()
