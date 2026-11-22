"""Lemma 2 filter (forced ramification + Riemann-Hurwitz) on centre-pair configurations.

For the relation pair (A, B -> C) with s = phi_A phi_B, d = phi_A / phi_B:
  (s + 1/s)(d + 1/d) = h_A + h_B,  (s - 1/s)(d - 1/d) = h_A - h_B,   h = phi^2 + phi^-2.
Relations: h3 = h1 + h2, h4 = h1 - h2, 2 h1 = h3 + h4, 2 h2 = h3 - h4.
Divisor identity at P (from div of both sides): for the relation whose right side is h_C,
  ord_P(s^2 + c) + ord_P(d^2 + c) - |e_A+e_B|_P - |e_A-e_B|_P = ord_P(phi_C^4 + 1) - 2|e_C|_P   (c = 1 for '+', -1 for '-')
so where |e_C,P| < M_P := max(|e_A,P|, |e_B,P|) the unit one of s, d (s if e_A = -e_B, d if e_A = e_B) takes a value
in {+-i} ('+') or {+-1} ('-') with ord_P(f - f(P)) >= 2 (M_P - |e_C,P|).
Riemann-Hurwitz on genus 1 for nonconstant f: sum_P (e_P - 1) = 2 deg f, where e_P = |ord_P f| at zeros/poles.
A configuration is EXCLUDED if some nonconstant f has forced ramification exceeding 2 deg f, or if a constant f is
forced to take two different kinds of value ({+-i} and {+-1}).
"""
import json
import sys
from collections import Counter, defaultdict
from pathlib import Path

RELS = [  # (A, B, C, kind): kind '+' -> values +-i, '-' -> values +-1
    (0, 1, 2, "+"), (0, 1, 3, "-"), (2, 3, 0, "+"), (2, 3, 1, "-"),
]


def check(cfg):
    pts = [(c[0], c[1:]) for c in cfg]
    forced = defaultdict(list)       # (fname) -> list of (P, min ramification, kind)
    for A, B, C, kind in RELS:
        for P, (mu, e) in enumerate(pts):
            M = max(abs(e[A]), abs(e[B]))
            if abs(e[C]) < M:
                if abs(e[A]) != abs(e[B]):
                    return "EXCLUDED: lemma1"      # cannot happen if Lemma 1 holds
                fname = ("s" if e[A] == -e[B] else "d", A, B)
                forced[fname].append((P, 2 * (M - abs(e[C])), kind))
    for fname, lst in forced.items():
        kind_, A, B = fname
        sign = 1 if kind_ == "s" else -1
        div = [e[A] + sign * e[B] for _, e in pts]
        deg = sum(x for x in div if x > 0)
        kinds = {k for _, _, k in lst}
        if deg == 0:
            if len(kinds) > 1:
                return f"EXCLUDED: constant {fname} forced to +-i and +-1"
            continue
        ram = sum(abs(x) - 1 for x in div if x != 0) + sum(r - 1 for _, r, _ in lst)
        if ram > 2 * deg:
            return f"EXCLUDED: RH {fname} ram {ram} > {2 * deg}"
        # each value's fibre: points forced to the same pair of values {v, -v}: sum of e <= 2 deg
        for k in kinds:
            if sum(r for _, r, kk in lst if kk == k) > 2 * deg:
                return f"EXCLUDED: fibre {fname}"
    return "SURVIVES"


def main():
    m = sys.argv[1]
    data = json.loads(Path(__file__).with_name(f"m{m}_configs.json").read_text())
    res = Counter()
    surv = []
    for d in data:
        r = check(d["cfg"])
        res[r.split(":")[0]] += 1
        if r == "SURVIVES":
            surv.append(d)
    print(res)
    print(Counter((tuple(d["mu"]), d["class"].split(" (")[0]) for d in surv))
    Path(__file__).with_name(f"m{m}_rh_survivors.json").write_text(json.dumps(surv))


if __name__ == "__main__":
    main()
