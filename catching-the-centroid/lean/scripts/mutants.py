#!/usr/bin/env python3
"""Mutation tests for LeanProofs/CentroidCircle.lean ("A random circle and the centroid", MSE 5101873):
every wrong variant must FAIL to check.

Each mutant copies the file to LeanProofs/CentroidCircleMut.lean with a single textual change and compiles it
with `lake env lean` (single process, nice 15). The unmutated copy must pass (baseline).
"""
import pathlib
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
SRC = ROOT / "LeanProofs" / "CentroidCircle.lean"
MUT = ROOT / "LeanProofs" / "CentroidCircleMut.lean"

MUTANTS = [
    ("key identity with 1/3 for 1/2", "theorem key (hρ : Dens ρ) : P ρ - 1 / 2 =",
     "theorem key (hρ : Dens ρ) : P ρ - 1 / 3 ="),
    ("three-sided bound claims 13/27", "      ρ (θ + π) ≤ ρ θ) :\n    P ρ ≤ 14 / 27 := by",
     "      ρ (θ + π) ≤ ρ θ) :\n    P ρ ≤ 13 / 27 := by"),
    ("Theorem 1 claims 1/55", "    |P ρ - 1 / 2| ≤ 1 / 54 := by", "    |P ρ - 1 / 2| ≤ 1 / 55 := by"),
    ("Theorem 1 with Stewart's 2/3 weakened to 3/5", "def Stewart (ρ : ℝ → ℝ) : Prop := 2 / 3 ≤ s ρ",
     "def Stewart (ρ : ℝ → ℝ) : Prop := 3 / 5 ≤ s ρ"),
    ("8/15 bound claims 33/62 (= 1/2 + 1/31)", "P ρ ≤ 8 / 15 := by", "P ρ ≤ 33 / 62 := by"),
    ("three sectors hold at most 3/5", "(∫ x in t₁ + π..t₂ + π, ρ x) ≤ 2 / 3 := by",
     "(∫ x in t₁ + π..t₂ + π, ρ x) ≤ 3 / 5 := by"),
    ("symmetral at least 7/10", "    2 / 3 ≤ s ρ := by", "    7 / 10 ≤ s ρ := by"),
    ("half-plane imbalance at most 1/20", "(θ : ℝ) : |b ρ θ| ≤ 1 / 18 := by", "(θ : ℝ) : |b ρ θ| ≤ 1 / 20 := by"),
    ("Grunbaum constant 2/3 instead of 5/9", "∫ x in θ..θ + π, ρ x ≤ 5 / 9", "∫ x in θ..θ + π, ρ x ≤ 2 / 3"),
    ("chord ratio 3 instead of 2", "def MinkRadon (ρ : ℝ → ℝ) : Prop := ∀ θ, ρ θ ≤ 4 * ρ (θ + π)",
     "def MinkRadon (ρ : ℝ → ℝ) : Prop := ∀ θ, ρ θ ≤ 9 * ρ (θ + π)"),
    ("symmetry under a quarter turn", "(hs : ∀ θ, ρ (θ + π) = ρ θ) : P ρ = 1 / 2",
     "(hs : ∀ θ, ρ (θ + π / 2) = ρ θ) : P ρ = 1 / 2"),
    ("signed area without the quarter-turn shift", "(1 / 2) * ∫ θ in (0 : ℝ)..2 * π, b ρ θ * db ρ (θ + π / 2)",
     "(1 / 2) * ∫ θ in (0 : ℝ)..2 * π, b ρ θ * db ρ θ"),
    ("product bound with G (1 - s) / 2", "    |P ρ - 1 / 2| ≤ G * (1 - s ρ) := by", "    |P ρ - 1 / 2| ≤ G * (1 - s ρ) / 2 := by"),
    ("symmetral mass misses the half", "theorem integral_abs_ρo (hρ : Dens ρ) : ∫ θ in (0 : ℝ)..2 * π, |ρo ρ θ| = 1 - s ρ",
     "theorem integral_abs_ρo (hρ : Dens ρ) : ∫ θ in (0 : ℝ)..2 * π, |ρo ρ θ| = 2 - 2 * s ρ"),
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
