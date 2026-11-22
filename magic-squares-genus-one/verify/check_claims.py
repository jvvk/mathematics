"""Assert every count stated in the paper (Table 1 and Section 7) from the outputs of the checking programs.

Runs the independent enumeration and filters (enum_indep.py), the certificate audits and the algebra checks, and
compares what they print with the numbers in the paper. Exits nonzero on the first mismatch. Reads the data files
that run_chain.sh writes; it does not regenerate them (m = 7 enumeration excepted, which is recomputed).
About two minutes.
"""

from __future__ import annotations

import ast
import re
import subprocess
import sys
from pathlib import Path

HERE = Path(__file__).parent

# Table 1 of the paper: admissible tables and the first condition that excludes each (enum_indep.py's labels).
TABLE1 = {
    4: (44, {"constant centre-pair function": 28, "repeated divisor up to sign": 16}),
    5: (93, {"base group law": 87, "group law": 6}),
    6: (
        2746,
        {
            "base group law": 1815,
            "constant centre-pair function": 72,
            "repeated divisor up to sign": 393,
            "fibre multiplicity": 12,
            "RH": 168,
            "group law": 260,
            "pencil": 24,
            "three affine": 1,
            "monomial relation, deg f = 2": 1,
        },
    ),
}
# Section 7: 8280 tables, 530 left by the conditions of Table 1; 296 + 100 + 24 further exclusions; 110 left.
M7_TABLES, M7_LEFT = 8280, 530
SEPTIC = {"residual fibre": 252, "two-fibre packing": 32, "tame reciprocity": 12}
RESIDUE, JETS, OPEN = 100, 24, 110
TORSION_CASES = 19
# Group-law certificates (Section 6): 87 + 6 in degree 5; 1815 + 260 in degree 6, of which 31 are torsion cases
# (19 with the centre-pair rows alone, 12 with the full-fibre rows).
GROUPLAW = {5: (93, {"integer": 93, "torsion": 0}), 6: (2075, {"integer": 2044, "torsion": 31})}


def run(*args: str) -> str:
    """Run one checking program. Its failure is a verdict (FAIL) when it exits through sys.exit or an
    AssertionError; any other exception is a crash, reported as CRASH with exit status 3, which the mutation
    suite counts as inconclusive rather than as a rejection."""
    p = subprocess.run([sys.executable, *args], cwd=HERE, capture_output=True, text=True)
    if p.returncode != 0:
        last = p.stderr.strip().splitlines()[-1] if p.stderr.strip() else ""
        crashed = p.returncode < 0 or p.returncode >= 128 or (
            "Traceback (most recent call last)" in p.stderr and not last.startswith("AssertionError"))
        tail = f"{p.stdout[-1500:]}\n{p.stderr[-1500:]}"
        if crashed:
            print(f"CRASH: python3 {' '.join(args)}: {last}\n{tail}")
            sys.exit(3)
        sys.exit(f"FAIL: python3 {' '.join(args)} exited {p.returncode}\n{tail}")
    return p.stdout


def dict_after(out: str, prefix: str = "{") -> dict:
    for line in out.splitlines():
        if line.startswith(prefix):
            return ast.literal_eval(line[line.index("{") :].rstrip(")"))
    sys.exit(f"FAIL: no line starting {prefix!r} in output")


def expect(name: str, got: object, want: object) -> None:
    if got != want:
        sys.exit(f"FAIL: {name}: got {got}, paper says {want}")
    print(f"ok  {name}: {got}")


def main() -> None:
    for m, (n, reasons) in TABLE1.items():
        out = run("enum_indep.py", str(m))
        n_got = int(
            re.search(
                rf"m={m}: independent tables (\d+), mconfigs tables (\d+), equal sets: True",
                out,
            )[1]
        )
        expect(f"degree {m} admissible tables", n_got, n)
        expect(f"degree {m} exclusions by condition", dict_after(out), reasons)
        expect(f"degree {m} survivors", re.search(r"survivors: (\d+)", out)[1], "0")
    out = run("enum_indep.py", "7")
    expect(
        "degree 7 admissible tables",
        int(re.search(r"m=7: independent tables (\d+)", out)[1]),
        M7_TABLES,
    )
    expect(
        "degree 7 left by Table 1 conditions",
        int(re.search(r"survivors: (\d+)", out)[1]),
        M7_LEFT,
    )

    run("check_centre_distinct_algebra.py")
    run("check_centre_sextic_algebra.py")
    run("verify_sec5.py")
    audit = run("audit_sextic.py")
    if "FAIL" in audit or "MISMATCH" in audit.upper():
        sys.exit("FAIL: audit_sextic.py disagrees with the certificates")
    tors = run("torsion_certificates.py", "6")
    expect(
        "degree 6 torsion-case certificates",
        int(
            re.search(
                r"m=6: (\d+) torsion-case certificates exported and checked", tors
            )[1]
        ),
        TORSION_CASES,
    )

    gl = run("check_grouplaw_certificates.py")
    for m, (n, kinds) in GROUPLAW.items():
        g = re.search(rf"m={m}: (\d+) group-law certificates checked; (\{{.*\}})", gl)
        expect(f"degree {m} group-law certificates", (int(g[1]), ast.literal_eval(g[2])), (n, kinds))

    sept = run("check_centre_septic.py")
    expect(
        "degree 7 septic exclusions",
        dict_after(sept[sept.index("m=7:") :].split("\n", 1)[0], "m=7"),
        SEPTIC,
    )
    run("check_septic_claude.py", "m7_fibre_reciprocity_certificates.json")
    run("m7_targets.py", "check")
    res = run("check_offcentre_residue.py")
    expect(
        "degree 7 residue exclusions",
        int(re.search(r"m=7: (\d+) exclusions", res)[1]),
        RESIDUE,
    )
    jets = run("check_septic_jets.py")
    m = re.search(
        r"m7_open134.json: (\d+) exclusions independently checked; (\d+) retained", jets
    )
    expect(
        "degree 7 jet exclusions (Codex filter, independent check)",
        (int(m[1]), int(m[2])),
        (JETS, OPEN),
    )
    mine = dict_after(run("jets_claude.py", "m7_open134.json"), "Counter(")
    expect(
        "degree 7 jet exclusions (Claude re-implementation)",
        mine,
        {"no seed": OPEN, "EXCLUDED (group law)": JETS},
    )
    print("ALL CLAIMS CHECKED")


if __name__ == "__main__":
    main()
