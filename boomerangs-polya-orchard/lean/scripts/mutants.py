#!/usr/bin/env python3
"""Mutation tests for LeanProofs/OrchardArcs.lean (boomerangs in Polya's orchard, MO 224015):
every wrong variant must FAIL to check.

Each mutant copies the file to LeanProofs/OrchardArcsMut.lean with a single textual change and compiles it
with `lake env lean` (single process, nice 15). The unmutated copy must pass (baseline).
"""
import pathlib
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
SRC = ROOT / "LeanProofs" / "OrchardArcs.lean"
MUT = ROOT / "LeanProofs" / "OrchardArcsMut.lean"

MUTANTS = [
    ("lower bound 4/r - 9", "theorem lower_value {r : ℝ} (h0 : 0 < r) (h1 : r ≤ 1 / 3) : 4 / r - 10 < 2 * (1 - r) / t0 r - (1 - r) := by",
     "theorem lower_value {r : ℝ} (h0 : 0 < r) (h1 : r ≤ 1 / 3) : 4 / r - 9 < 2 * (1 - r) / t0 r - (1 - r) := by"),
    ("t0 shifted by r in the denominator", "noncomputable def t0 (r : ℝ) : ℝ := r * (1 - r) / (A r + S r)",
     "noncomputable def t0 (r : ℝ) : ℝ := r * (1 - r) / (A r + S r + r)"),
    ("rise box too tall", "    (hy1 : y ≤ 1 - r) (i j : ℤ) (hij : (i, j) ≠ (0, 0)) : r ^ 2 ≤ (x - i) ^ 2 + (y - j) ^ 2 := by",
     "    (hy1 : y ≤ 1) (i j : ℤ) (hij : (i, j) ≠ (0, 0)) : r ^ 2 ≤ (x - i) ^ 2 + (y - j) ^ 2 := by"),
    ("corridor from x = 0", "theorem corridor_clear {r x y : ℝ} (hx0 : r ≤ x) (hx1 : x ≤ 1 - r) (hr : 0 ≤ r) (i j : ℤ) :",
     "theorem corridor_clear {r x y : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1 - r) (hr : 0 ≤ r) (i j : ℤ) :"),
    ("arc height window too wide", "    (hstart : r ≤ -a * c + Real.sqrt (a ^ 2 - (1 - r - a * s) ^ 2)) (hy : |y - a * s| ≤ a * s - (1 - r)) :",
     "    (hstart : r ≤ -a * c + Real.sqrt (a ^ 2 - (1 - r - a * s) ^ 2)) (hy : |y - a * s| ≤ a * s) :"),
    ("start condition reversed", "    (hq : K r * t ^ 2 - 2 * A r * t + r * (1 - r) ≤ 0) :",
     "    (hq : 0 ≤ K r * t ^ 2 - 2 * A r * t + r * (1 - r)) :"),
    ("corridor slope 4r/m", "    (hε : ε < π / 2) (htan : Real.tan ε < 2 * r / m) (hlo : τ₀ ≤ τk - r)",
     "    (hε : ε < π / 2) (htan : Real.tan ε < 4 * r / m) (hlo : τ₀ ≤ τk - r)"),
    ("Farey angle pi/(2Q)", "    θ < π / Q := by\n  have hJ", "    θ < π / (2 * Q) := by\n  have hJ"),
    ("Minkowski offset 0.2 r", "    (ht : t ≤ 3 / (2 * r)) : a - Real.sqrt (a ^ 2 - t ^ 2) ≤ 29 / 100 * r ∧ 2 / 3 * r + 29 / 100 * r < r := by",
     "    (ht : t ≤ 3 / (2 * r)) : a - Real.sqrt (a ^ 2 - t ^ 2) ≤ 20 / 100 * r ∧ 2 / 3 * r + 20 / 100 * r < r := by"),
    ("epsilon factor 0.99", "noncomputable def eps (a r m : ℝ) : ℝ := 101 / 100 * Real.sqrt (2 * (1 / m + 2 * r) / a)",
     "noncomputable def eps (a r m : ℝ) : ℝ := 99 / 100 * Real.sqrt (2 * (1 / m + 2 * r) / a)"),
    ("middle bound 20/r^2", "        28 / r ^ 2 := by\n  have hapos", "        20 / r ^ 2 := by\n  have hapos"),
]


def check(text: str) -> bool:
    MUT.write_text(text)
    r = subprocess.run(["nice", "-n", "15", "lake", "env", "lean", str(MUT)], cwd=ROOT,
                       capture_output=True, text=True, timeout=900)
    return r.returncode == 0 and "error" not in r.stdout


def main() -> int:
    src = SRC.read_text()
    bad = 0
    try:
        if not check(src):
            print("BASELINE FAILS")
            return 1
        print("baseline: passes")
        for name, old, new in MUTANTS:
            if src.count(old) != 1:
                print(f"SETUP ERROR ({src.count(old)} matches): {name}")
                bad += 1
                continue
            ok = check(src.replace(old, new))
            print(f"{'SURVIVED' if ok else 'rejected'}: {name}")
            bad += ok
    finally:
        MUT.unlink(missing_ok=True)
    print(f"{len(MUTANTS) - bad}/{len(MUTANTS)} mutants rejected")
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
