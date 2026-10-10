#!/usr/bin/env python3
"""Mutation tests for LeanProofs/SevenColours (colour the points, MSE 1381502): every wrong
variant must FAIL to check.

Each mutant copies one file to SevenColours/Mut.lean with a single textual change and compiles it
with `lake env lean` (single process, background QoS). Unmutated copies must pass (baseline).
"""
import os
import pathlib
import signal
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
D = ROOT / "LeanProofs" / "SevenColours"
MUT = D / "Mut.lean"

MUTANTS = [
    ("lemma bound 9/10", "Basic.lean",
     "(hc : √3 / 2 ≤ c) : r₁ ^ 2 + r₂ ^ 2 - 2 * r₁ * r₂ * c ≤ 1 := by",
     "(hc : √3 / 2 ≤ c) : r₁ ^ 2 + r₂ ^ 2 - 2 * r₁ * r₂ * c ≤ 9 / 10 := by"),
    ("lemma at sixty degrees", "Basic.lean",
     "(hc : √3 / 2 ≤ c) : r₁ ^ 2 + r₂ ^ 2 - 2 * r₁ * r₂ * c ≤ 1 := by",
     "(hc : 1 / 2 ≤ c) : r₁ ^ 2 + r₂ ^ 2 - 2 * r₁ * r₂ * c ≤ 1 := by"),
    ("ratio decreasing", "Basic.lean",
     "    A / (√A + c) ^ 2 ≤ B / (√B + c) ^ 2 := by", "    B / (√B + c) ^ 2 ≤ A / (√A + c) ^ 2 := by"),
    ("density 1/(1 + √3)", "Basic.lean",
     "theorem density_eq : (π / 4) / (√(π / 4) + √π * (√3 / 2)) ^ 2 = 1 / (1 + √3) ^ 2 := by",
     "theorem density_eq : (π / 4) / (√(π / 4) + √π * (√3 / 2)) ^ 2 = 1 / (1 + √3) := by"),
    ("density below 1/8", "Basic.lean",
     "theorem density_lt : 1 / (1 + √3) ^ 2 < 1 / 7 := by", "theorem density_lt : 1 / (1 + √3) ^ 2 < 1 / 8 := by"),
    ("nine colours forced", "Basic.lean",
     "theorem colours_ge_eight (k : ℕ) (hk : (1 : ℝ) ≤ k * (1 / (1 + √3) ^ 2)) : 8 ≤ k := by",
     "theorem colours_ge_eight (k : ℕ) (hk : (1 : ℝ) ≤ k * (1 / (1 + √3) ^ 2)) : 9 ≤ k := by"),
    ("witness outside its hexagon", "Basic.lean",
     "InHex (centre 3 (-1)) (1.8, √3 / 4)", "InHex (centre 3 (-1)) (1.2, √3 / 4)"),
    ("witnesses closer than √2", "Basic.lean",
     "(1.8 - 0.45) ^ 2 + (√3 / 4 - 0) ^ 2 < 3 := by", "(1.8 - 0.45) ^ 2 + (√3 / 4 - 0) ^ 2 < 2 := by"),
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
