"""Export a certificate for every group-law exclusion in degrees five and six (Table 1 of the paper).

A table is excluded by the group law when its principal divisors force two of its points to coincide. The relation
rows are the four centre-pair divisors and, for the rows marked (R4), divisors Z_f - delta P where P is a forced
point of the pair monomial f of degree delta with multiplicity delta. The certificate is either

  - an integer vector y with sum_i y_i row_i = P_j - P_k, which makes P_j - P_k principal, so P_j = P_k; or
  - when no such combination exists (the 19 torsion cases of degree six, and any others), the Smith-form torsion
    certificate of torsion_certificates.py.

Classification follows enum_indep.py exactly: "base group law" uses the centre-pair rows only, "group law" adds the
full-fibre rows. Writes m{5,6}_grouplaw_certificates.json; check_grouplaw_certificates.py checks them with
separately written code.
"""

from __future__ import annotations

import itertools
import json
import sys
from pathlib import Path

import sympy as S
from sympy.matrices.normalforms import smith_normal_decomp

from audit_sextic import deg, forced, mono_div, rows_of, verdict
from centre_distinct import reason as distinct_reason
from enum_indep import enumerate_all
from grouplaw_exact import decide
from torsion_certificates import certificate as torsion_certificate

HERE = Path(__file__).parent
EXPECTED = {
    5: {"base group law": 87, "group law": 6},
    6: {"base group law": 1815, "group law": 260},
}


def full_fibre_rows(cfg: list[list[int]]) -> list[dict]:
    """The (R4) rows of audit_sextic.ram_and_relations, with the monomial and point that justify each."""
    rows = rows_of(cfg)
    out = []
    for i, j in itertools.combinations(range(4), 2):
        for sj in (1, -1):
            u = [0] * 4
            u[i], u[j] = 1, sj
            d = mono_div(u, rows)
            dl = deg(d)
            if dl == 0:
                continue
            for p, (_, r) in forced(u, cfg).items():
                if r == dl:
                    rel = [max(t, 0) for t in d]
                    rel[p] -= dl
                    out.append(
                        {"monomial": [i, j, sj], "point": p, "degree": dl, "row": rel}
                    )
    return out


def integer_combination(R: list[list[int]], target: list[int]) -> list[int] | None:
    """An integer y with y R = target, or None."""
    M = S.Matrix(R)
    D, U, V = smith_normal_decomp(M, domain=S.ZZ)  # D = U M V
    tV = S.Matrix([target]) * V
    r = sum(1 for k in range(min(D.shape)) if D[k, k] != 0)
    if any(tV[k] != 0 for k in range(r, M.cols)):
        return None
    if any(tV[k] % D[k, k] for k in range(r)):
        return None
    z = S.zeros(1, M.rows)
    for k in range(r):
        z[k] = tV[k] // D[k, k]
    y = z * U
    assert list(S.Matrix([list(map(int, y))]) * M) == list(target)
    return [int(t) for t in y]


def certify(cfg: list[list[int]], extra: list[dict]) -> dict:
    n = len(cfg)
    R = [list(r) for r in rows_of(cfg) if any(r)] + [e["row"] for e in extra]
    for j, k in itertools.combinations(range(n), 2):
        y = integer_combination(R, [int(p == j) - int(p == k) for p in range(n)])
        if y is not None:
            return {"kind": "integer", "rows": R, "y": y, "points": [j, k]}
    return {
        "kind": "torsion",
        "rows": R,
        "torsion": torsion_certificate([r[1:] for r in R], n),
    }


def main() -> None:
    for m in (5, 6):
        out, counts = [], {"base group law": 0, "group law": 0}
        for tab in sorted(enumerate_all(m)):
            cfg = [list(c) for c in tab]
            rows = rows_of(cfg)
            if decide([r[1:] for r in rows if any(r)], len(cfg)) == "none":
                kind, extra = "base group law", []
            elif distinct_reason(cfg) == "survives" and verdict(cfg) == "group law":
                kind, extra = "group law", full_fibre_rows(cfg)
            else:
                continue
            counts[kind] += 1
            out.append(
                {
                    "cfg": cfg,
                    "condition": kind,
                    "full_fibre": extra,
                    "certificate": certify(cfg, extra),
                }
            )
        (HERE / f"m{m}_grouplaw_certificates.json").write_text(
            json.dumps(out, default=int) + "\n"
        )
        kinds = {
            c: sum(1 for e in out if e["certificate"]["kind"] == c)
            for c in ("integer", "torsion")
        }
        print(f"m={m}: {counts}; certificates {kinds}")
        if counts != EXPECTED[m]:
            sys.exit(
                f"FAIL: degree {m} group-law exclusions {counts}, expected {EXPECTED[m]}"
            )


if __name__ == "__main__":
    main()
