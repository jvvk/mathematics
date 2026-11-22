"""Write the degree-seven target lists between the filters, or check them.

  m7_targets.py split   after centre_septic.py: split its 234 survivors by whether some pair monomial
                        phi_i phi_j^s (i < j, s = +-1) has degree two; writes m7_deg2_targets.json (60) and
                        m7_offcentre_targets.json (174, the input of offcentre_residue.py)
  m7_targets.py open    after offcentre_residue.py: writes m7_open134.json, its 74 survivors followed by the 60
                        (the input of the jet filters)
  m7_targets.py check   recompute all three and fail if the files differ

These lists were first written by hand (October 2026); this script reproduces them exactly.
"""

from __future__ import annotations

import json
import sys
from pathlib import Path

from audit_sextic import deg, mono_div, rows_of

HERE = Path(__file__).parent


def load(name: str) -> list[dict]:
    return json.loads((HERE / name).read_text())


def deg2_monomials(cfg: list[list[int]]) -> list[list[int]]:
    rows = rows_of(cfg)
    out = []
    for i in range(4):
        for j in range(i + 1, 4):
            for s in (1, -1):
                u = [0, 0, 0, 0]
                u[i], u[j] = 1, s
                if deg(mono_div(u, rows)) == 2:
                    out.append([i, j, s])
    return out


def lists() -> dict[str, list[dict]]:
    surv = load("m7_fibre_reciprocity_survivors.json")
    tagged = [dict(d, deg2=deg2_monomials(d["cfg"])) for d in surv]
    deg2 = [d for d in tagged if d["deg2"]]
    out = {"m7_deg2_targets.json": deg2, "m7_offcentre_targets.json": [d for d in tagged if not d["deg2"]]}
    if (HERE / "m7_residue_survivors.json").exists():
        residue = load("m7_residue_survivors.json")
        out["m7_open134.json"] = [{"cfg": d["cfg"], "k": d["k"], "source": "offcentre"} for d in residue] + [
            {"cfg": d["cfg"], "k": d["k"], "source": "deg2", "deg2": d["deg2"]} for d in deg2
        ]
    return out


def main() -> None:
    mode = sys.argv[1] if len(sys.argv) > 1 else "check"
    want = lists()
    names = {"split": ["m7_deg2_targets.json", "m7_offcentre_targets.json"], "open": ["m7_open134.json"],
             "check": list(want)}[mode]
    if any(n not in want for n in names):
        sys.exit("FAIL: run offcentre_residue.py before m7_targets.py open")
    sizes = {n: len(want[n]) for n in names}
    print(sizes)
    expected = {"m7_deg2_targets.json": 60, "m7_offcentre_targets.json": 174, "m7_open134.json": 134}
    if any(sizes[n] != expected[n] for n in names):
        sys.exit(f"FAIL: list sizes {sizes}, expected {expected}")
    if mode == "check":
        bad = [n for n in names if load(n) != want[n]]
        if bad:
            sys.exit(f"FAIL: {bad} differ from the recomputed lists")
        print("target lists: recomputed and equal")
    else:
        for n in names:
            (HERE / n).write_text(json.dumps(want[n]) + "\n")
        print("wrote", ", ".join(names))


if __name__ == "__main__":
    main()
