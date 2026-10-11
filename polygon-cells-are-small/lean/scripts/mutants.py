#!/usr/bin/env python3
"""Mutation tests for LeanProofs/PolygonCells (polygon cells, MO 436753): every wrong
variant must FAIL to check.

Each mutant copies one file to PolygonCells/Mut.lean with a single textual change and compiles it
with `lake env lean` (single process, background QoS). Unmutated copies must pass (baseline).
"""
import os
import pathlib
import signal
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
D = ROOT / "LeanProofs" / "PolygonCells"
MUT = D / "Mut.lean"

MUTANTS = [
    ("drop parity of a", "Basic.lean", "theorem coprime_sub_add (a b : ℤ) (ha : Odd a) (hb : Even b)",
     "theorem coprime_sub_add (a b : ℤ) (ha : Even a) (hb : Even b)"),
    ("level without parity witness", "Basic.lean", "  · rw [Int.modEq_iff_dvd]; exact ⟨k * y, by ring⟩",
     "  · rw [Int.modEq_iff_dvd]; exact ⟨k * x, by ring⟩"),
    ("spacing (b, a) instead of (2b, 2a)", "Basic.lean", "∃ m : ℤ, u - u' = 2 * b * m ∧ v - v' = 2 * a * m",
     "∃ m : ℤ, u - u' = 4 * b * m ∧ v - v' = 4 * a * m"),
    ("inradius 1/(2 cos)", "Basic.lean", "(1 / (2 * sin t)) * sin (t / 2) = 1 / (4 * cos (t / 2))",
     "(1 / (2 * sin t)) * sin (t / 2) = 1 / (2 * cos (t / 2))"),
    ("central gap up to pi/2", "Basic.lean", "(h1 : t < π / 3)", "(h1 : t < π / 2)"),
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
