"""Check the group-law certificates of grouplaw_certificates.py without the code that produced them.

For every certificate: each relation row must be a centre-pair divisor read off the table, or a full-fibre row
Z_f - delta P whose forced multiplicity delta is recomputed with centre_sextic.all_forced (Codex's implementation,
not audit_sextic.forced which found the rows); an integer certificate must satisfy sum y_i row_i = P_j - P_k
exactly with j != k; a torsion certificate is checked by torsion_certificates.check. Also checks that every table
is admissible and that the certified tables are exactly as many as Table 1 says.
"""

from __future__ import annotations

import json
import sys
from pathlib import Path

from centre_sextic import all_forced, degree, monomial_divisor
from torsion_certificates import check as check_torsion

HERE = Path(__file__).parent
EXPECTED = {
    5: 93,
    6: 2075,
}  # base group law + group law with full-fibre rows: 87 + 6 and 1815 + 260


def admissible(cfg: list[list[int]], m: int) -> bool:
    if sum(c[0] for c in cfg) != m:
        return False
    for c in cfg:
        mu, e = c[0], c[1:]
        if any(abs(t) > mu for t in e) or sum(abs(t) == mu for t in e) < 3:
            return False
    rows = [[c[1 + i] for c in cfg] for i in range(4)]
    return all(sum(r) == 0 and sum(max(t, 0) for t in r) != 1 for r in rows)


def legitimate_rows(cfg: list[list[int]]) -> set[tuple[int, ...]]:
    rows = [[c[1 + i] for c in cfg] for i in range(4)]
    ok = {tuple(r) for r in rows if any(r)}
    F = all_forced(cfg)
    for (i, j, sign), items in F.items():
        v = [0] * 4
        v[i], v[j] = 1, sign
        d = monomial_divisor(v, rows)
        dl = degree(d)
        for p, mult, _ in items:
            if dl and mult == dl:
                rel = [max(t, 0) for t in d]
                rel[p] -= dl
                ok.add(tuple(rel))
    return ok


def main() -> None:
    for m, want in EXPECTED.items():
        data = json.loads((HERE / f"m{m}_grouplaw_certificates.json").read_text())
        seen = set()
        for k, e in enumerate(data):
            cfg, cert = e["cfg"], e["certificate"]
            n = len(cfg)
            if not admissible(cfg, m):
                sys.exit(f"FAIL: m={m} entry {k} is not an admissible table")
            key = json.dumps(cfg)
            if key in seen:
                sys.exit(f"FAIL: m={m} entry {k} repeated")
            seen.add(key)
            legit = legitimate_rows(cfg)
            if any(tuple(r) not in legit for r in cert["rows"]):
                sys.exit(
                    f"FAIL: m={m} entry {k} uses a row that is not a principal divisor of the table"
                )
            if cert["kind"] == "integer":
                j, kk = cert["points"]
                comb = [
                    sum(y * r[p] for y, r in zip(cert["y"], cert["rows"]))
                    for p in range(n)
                ]
                if j == kk or comb != [int(p == j) - int(p == kk) for p in range(n)]:
                    sys.exit(f"FAIL: m={m} entry {k}: combination is not P_j - P_k")
            else:
                t = cert["torsion"]
                if [list(r[1:]) for r in cert["rows"]] != [
                    list(r) for r in t["A"]
                ] or not check_torsion(t, n):
                    sys.exit(
                        f"FAIL: m={m} entry {k}: torsion certificate does not check"
                    )
        kinds = {
            c: sum(1 for e in data if e["certificate"]["kind"] == c)
            for c in ("integer", "torsion")
        }
        print(f"m={m}: {len(data)} group-law certificates checked; {kinds}")
        if len(data) != want:
            sys.exit(
                f"FAIL: m={m}: {len(data)} certificates, Table 1 has {want} group-law exclusions"
            )
    print("group-law certificates: all checked")


if __name__ == "__main__":
    main()
