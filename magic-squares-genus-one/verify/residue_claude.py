"""Claude's independent check of Codex's residue obstruction (OFFCENTRE_RESIDUES.md), by direct Groebner bases.

Unknowns a[i][P] = residue of (A_i / t00) * omega at the simple centre zero P (A_1..A_4 = cells (1,0), (0,1), (1,1),
(1,-1)); a[i][P] = 0 when eps_iP = 0, and nonzero otherwise. Necessary conditions:
  - residue theorem for A_i/t00 and B_i/t00 (B_i(P) = i eps_iP A_i(P)): sum_{eps=+1} a_iP = 0 = sum_{eps=-1} a_iP;
  - e(P) = 0: a_3P^2 = a_1P^2 + a_2P^2 and a_4P^2 = a_1P^2 - a_2P^2.
The system is homogeneous; a solution with all required residues nonzero exists iff the ideal plus
1 - z * prod(nonzero residues) is not the unit ideal (Singular std over Q, which decides it over C).
"""

from __future__ import annotations

import json
import subprocess
import sys
import tempfile
from collections import Counter
from pathlib import Path

HERE = Path(__file__).parent


def system(cfg):
    n = len(cfg)
    var = {}
    for p, col in enumerate(cfg):
        assert col[0] == 1, "simple points only"
        for i in range(4):
            if col[1 + i] != 0:
                var[(i, p)] = f"a{i}_{p}"

    def a(i, p):
        return var.get((i, p), "0")

    eqs = []
    for i in range(4):
        for sgn in (1, -1):
            terms = [a(i, p) for p in range(n) if cfg[p][1 + i] == sgn]
            if terms:
                eqs.append("+".join(terms))
    for p in range(n):
        eqs.append(f"({a(2, p)})^2-({a(0, p)})^2-({a(1, p)})^2")
        eqs.append(f"({a(3, p)})^2-({a(0, p)})^2+({a(1, p)})^2")
    names = sorted(var.values())
    rab = "1-zz*" + "*".join(names)
    return names, eqs + [rab]


def unit(names, eqs, timeout=120):
    script = (
        f"ring R=0,({','.join(names)},zz),dp; option(redSB);\n"
        f"ideal J={','.join(eqs)};\nideal G=std(J);\n"
        'if (size(G)==1 && deg(G[1])==0) {print("UNIT");} else {print("NONUNIT");}\nquit;\n'
    )
    with tempfile.NamedTemporaryFile("w", suffix=".sing", delete=False) as fh:
        fh.write(script)
    try:
        r = subprocess.run(["Singular", "-q", fh.name], capture_output=True, text=True, timeout=timeout)
    except subprocess.TimeoutExpired:
        return "TIMEOUT"
    words = r.stdout.strip().split()
    if r.returncode != 0 or r.stderr.strip() or len(words) != 1 or words[0] not in ("UNIT", "NONUNIT"):
        return "ERROR"
    return words[0]


def main():
    """residue_claude.py <tables.json> [indices...]  or  residue_claude.py <tables.json> --expect-unit <certs.json>

    With --expect-unit, the indices are those excluded in <certs.json> (offcentre_residue.py's certificates), and
    every one of them must come out UNIT (the system has no solution); NONUNIT, TIMEOUT or ERROR fails.
    """
    src = sys.argv[1]
    data = json.loads((HERE / src).read_text())
    expect = "--expect-unit" in sys.argv
    if expect:
        certs = json.loads((HERE / sys.argv[sys.argv.index("--expect-unit") + 1]).read_text())
        only = sorted(e["index"] for e in certs["exclusions"])
    else:
        only = [int(a) for a in sys.argv[2:]]
    res = {}
    for k, d in enumerate(data):
        if only and k not in only:
            continue
        names, eqs = system(d["cfg"])
        res[k] = unit(names, eqs)
        print(k, res[k], flush=True)
    (HERE / f"residue_claude_{Path(src).stem}.json").write_text(json.dumps(res, indent=1) + "\n")
    print(Counter(res.values()))
    if any(v in ("TIMEOUT", "ERROR") for v in res.values()):
        sys.exit("FAIL: inconclusive Singular runs: " + ", ".join(str(k) for k, v in res.items() if v in ("TIMEOUT", "ERROR")))
    if expect:
        bad = [k for k, v in res.items() if v != "UNIT"]
        if bad or len(res) != len(only):
            sys.exit(f"FAIL: {len(bad)} of the {len(only)} certified residue exclusions are not confirmed: {bad}")
        print(f"all {len(only)} residue exclusions confirmed (UNIT)")


if __name__ == "__main__":
    main()
