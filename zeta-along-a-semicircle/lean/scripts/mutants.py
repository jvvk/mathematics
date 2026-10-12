#!/usr/bin/env python3
"""Mutation tests for LeanProofs/ZetaArc (zeta on a semicircle, MSE 5150160): every wrong
variant must FAIL to check.

Each mutant copies one file to ZetaArc/Mut.lean with a single textual change and compiles it
with `lake env lean` (single process, background QoS). Unmutated copies must pass (baseline).
"""
import os
import pathlib
import signal
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
D = ROOT / "LeanProofs" / "ZetaArc"
MUT = D / "Mut.lean"

MUTANTS = [
    ("cot without the 1/2", "Basic.lean", "      Real.cos (u / 2) / (2 * Real.sin (u / 2)) := by",
     "      Real.cos (u / 2) / Real.sin (u / 2) := by"),
    ("log derivative with a minus", "Basic.lean", "= 1 / (z - z₀) + h' / h := by", "= 1 / (z - z₀) - h' / h := by"),
    ("region A without the radius", "Basic.lean", "(hgap : r * M < c)", "(hgap : M < c)"),
    ("R vanishes at pi/2", "Basic.lean", "((-(r : ℂ) * I * exp (Real.pi * I)) * ((a : ℂ) / b)).re = 0",
     "((-(r : ℂ) * I * exp (Real.pi / 2 * I)) * ((a : ℂ) / b)).re = 0"),
    ("non-strict derivative", "Basic.lean", "HasDerivAt R (deriv R x) x ∧ deriv R x < 0)",
     "HasDerivAt R (deriv R x) x ∧ deriv R x ≤ 0)"),
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
