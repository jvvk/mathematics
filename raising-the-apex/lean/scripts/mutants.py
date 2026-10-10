#!/usr/bin/env python3
"""Mutation tests for LeanProofs/GaussianApex.lean ("Raising the apex", MO 499635):
every wrong variant must FAIL to check.

Each mutant copies the file to LeanProofs/GaussianApexMut.lean with a single textual change and compiles it
with `lake env lean` (single process, nice 15). The unmutated copy must pass (baseline).
"""
import pathlib
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
SRC = ROOT / "LeanProofs" / "GaussianApex.lean"
MUT = ROOT / "LeanProofs" / "GaussianApexMut.lean"

MUTANTS = [
    ("equal-length increments grow to the right", "    (hL : 0 < L) : φ (u₂ + L) - φ u₂ ≤ φ (u₁ + L) - φ u₁ := by", "    (hL : 0 < L) : φ (u₁ + L) - φ u₁ ≤ φ (u₂ + L) - φ u₂ := by"),
    ("monotone instead of strictly", "theorem increment_gt {φ : ℝ → ℝ} (hc : ConcaveOn ℝ (Ioi 0) φ) (hm : StrictMonoOn φ (Ioi 0))", "theorem increment_gt {φ : ℝ → ℝ} (hc : ConcaveOn ℝ (Ioi 0) φ) (hm : MonotoneOn φ (Ioi 0))"),
    ("longer interval starts later", "(hu₁ : 0 < u₁) (hv₂ : u₂ < v₂) (hu : u₁ ≤ u₂)", "(hu₁ : 0 < u₁) (hv₂ : u₂ < v₂) (hu : u₂ ≤ u₁)"),
    ("apex lowered", "{h₁ h₂ y y' : ℝ} (hh₁ : 0 < h₁) (hh : h₁ < h₂)", "{h₁ h₂ y y' : ℝ} (hh₁ : 0 < h₁) (hh : h₂ < h₁)"),
    ("scale s1 + s2", "= D + ((1 - l) * s₁ + l * s₂) • (z - D) := by", "= D + (s₁ + s₂) • (z - D) := by"),
    ("double integral without the 2", "      = 2 * ((μ univ).toReal * ∫ x, f x * g x ∂μ - (∫ x, f x ∂μ) * ∫ x, g x ∂μ) := by", "      = ((μ univ).toReal * ∫ x, f x * g x ∂μ - (∫ x, f x ∂μ) * ∫ x, g x ∂μ) := by"),
    ("Chebyshev reversed", "    (∫ x, f x ∂μ) * (∫ x, g x ∂μ) ≤ (μ univ).toReal * ∫ x, f x * g x ∂μ := by", "    (μ univ).toReal * ∫ x, f x * g x ∂μ ≤ (∫ x, f x ∂μ) * (∫ x, g x ∂μ) := by"),
    ("strict Chebyshev from a null set", "    (hpos : 0 < (μ.prod μ)", "    (hpos : 0 ≤ (μ.prod μ)"),
    ("added mass below", "(h₁ : m₀ < m₁) (h₂ : m₁ ≤ m₂) :", "(h₁ : m₀ < m₁) (h₂ : m₂ ≤ m₁) :"),
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
