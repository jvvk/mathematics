#!/usr/bin/env python3
"""Mutation tests for LeanProofs/OpenSolids (incomplete open solids, MO 508521): every wrong
variant must FAIL to check.

Each mutant copies one file to OpenSolids/Mut.lean with a single textual change and compiles it
with `lake env lean` (single process, background QoS). Unmutated copies must pass (baseline).
"""
import os
import pathlib
import signal
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
D = ROOT / "LeanProofs" / "OpenSolids"
MUT = D / "Mut.lean"

MUTANTS = [
    ("cube joins bits differing by 3", "Basic.lean", "a ^^^ b == 4", "a ^^^ b == 3"),
    ("reflections instead of rotations", "Basic.lean", "if sgn3 p == (flips % 2 == 0)", "if sgn3 p != (flips % 2 == 0)"),
    ("tree test without connectivity", "Basic.lean", " && (grow t)^[8] (2 ^ low M) == M", ""),
    ("edge half-turns 5", "Basic.lean", ".count [2, 10, 0, 0] = 6", ".count [2, 10, 0, 0] = 5"),
    ("Burnside 48 -> 46", "Basic.lean", "38 * X ^ 5 + 48 * X ^ 6", "38 * X ^ 5 + 46 * X ^ 6"),
    ("cube six vertices span 6", "Basic.lean", "(fun S => induced S cube ≤ 7)", "(fun S => induced S cube ≤ 6)"),
    ("octahedron three vertices span 2", "Basic.lean", "(fun S => induced S oct ≤ 3)", "(fun S => induced S oct ≤ 2)"),
    ("ladder 14 trees", "Basic.lean", "(trees (delete [0, 1] cube)).length = 15", "(trees (delete [0, 1] cube)).length = 14"),
    ("ladder half-turn fixes 4", "Basic.lean", "= [15, 3]", "= [15, 4]"),
    ("hub two spokes 22", "Basic.lean", "(spokes 7 · == 2)).length = 24", "(spokes 7 · == 2)).length = 22"),
    ("hub third-turns fix none", "Basic.lean", "= [50, 2, 2]", "= [50, 0, 0]"),
    ("wheel 44 trees", "Basic.lean", "(trees (delete [5] oct)).length = 45", "(trees (delete [5] oct)).length = 44"),
    ("wheel half-turn fixes 3", "Basic.lean", ".count 5 = 1", ".count 3 = 1"),
    ("K4 minus edge 7 trees", "Basic.lean", "(trees (delete [0, 2] oct)).length = 8", "(trees (delete [0, 2] oct)).length = 7"),
    ("cube correction 38 - 5", "Basic.lean", "38 - 6 = 32", "38 - 5 = 32"),
    ("octahedron 186", "Basic.lean", "5 + 1 = 185", "5 + 1 = 186"),
]


def check(text: str) -> bool:
    MUT.write_text(text)
    p = subprocess.Popen(["taskpolicy", "-c", "background", "lake", "env", "lean", str(MUT)], cwd=ROOT,
                         stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True,
                         start_new_session=True)
    try:
        out, _ = p.communicate(timeout=1200)
    except subprocess.TimeoutExpired:
        os.killpg(p.pid, signal.SIGKILL)  # lake's lean child too
        p.communicate()
        print("  (timed out: counted as not compiling)", flush=True)
        return False
    return p.returncode == 0 and "error" not in out


def main() -> int:
    bad = 0
    sel = [m for m in MUTANTS if not sys.argv[1:] or any(a in m[1] for a in sys.argv[1:])]
    try:
        for f in sorted({m[1] for m in sel}):
            ok = check((D / f).read_text())
            print(f"baseline {'ok' if ok else 'FAILS'}: {f}", flush=True)
            bad += not ok
        for name, f, old, new in sel:
            src = (D / f).read_text()
            if src.count(old) != 1:
                print(f"MUTATION DID NOT APPLY: {name}", flush=True)
                bad += 1
                continue
            if check(src.replace(old, new)):
                print(f"MUTANT SURVIVED: {name}", flush=True)
                bad += 1
            else:
                print(f"rejected: {name}", flush=True)
    finally:
        MUT.unlink(missing_ok=True)
    print(f"{len(sel)} mutants, {bad} problems")
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
