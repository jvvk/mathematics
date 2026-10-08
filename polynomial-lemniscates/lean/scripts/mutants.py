"""Mutation test for LeanProofs/Lemniscates: each mutant plants a wrong claim; Lean must reject it.

    python3 scripts/mutants.py   (from lean/, after lake build)
"""
from __future__ import annotations

import pathlib
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
DIR = ROOT / "LeanProofs" / "Lemniscates"

MUTANTS: list[tuple[str, str, str]] = [
    ("Pairing", "(S.filter (fun p => σ p = p)).card ≤ 6 := by", "(S.filter (fun p => σ p = p)).card ≤ 5 := by"),
    ("Liouville", "(hb : ∀ z, ‖f z‖ ≤ A + B * Real.sqrt ‖z‖)", "(hb : ∀ z, ‖f z‖ ≤ A + B * ‖z‖)"),
    ("TheoremA", "hfin.toFinset.card ≤ 2 * P₁.natDegree * P₂.natDegree - 2 := by", "hfin.toFinset.card ≤ 2 * P₁.natDegree * P₂.natDegree - 3 := by"),
    ("Corollaries", "(F : Finset ℂ) (hF : ∀ z ∈ F, z ∈ oval a b ρ₁ ∧ z ∈ oval c d ρ₂) : F.card ≤ 6 := by", "(F : Finset ℂ) (hF : ∀ z ∈ F, z ∈ oval a b ρ₁ ∧ z ∈ oval c d ρ₂) : F.card ≤ 5 := by"),
    ("Corollaries", "theorem bernoulli_six : ∃ F : Finset ℂ, F.card = 6 ∧", "theorem bernoulli_six : ∃ F : Finset ℂ, F.card = 7 ∧"),
    ("Corollaries", "    M n₁ n₂ = 2 * n₁ * n₂ - 2 ↔ (n₁ = 2 ∧ n₂ = 2) ∨ (n₁ = 2 ∧ n₂ = 3) := by", "    M n₁ n₂ = 2 * n₁ * n₂ - 2 ↔ (n₁ = 2 ∧ n₂ = 2) ∨ (n₁ = 2 ∧ n₂ = 4) := by"),
    ("CaseI", "F.card ≤ 2 * f₁.natDegree * f₂.natDegree - 2 := by\n  set n₁", "F.card ≤ 2 * f₁.natDegree * f₂.natDegree - 3 := by\n  set n₁"),
    ("CaseI", "S.card = f₁.natDegree * g₂.natDegree + f₂.natDegree * g₁.natDegree ∧", "S.card = f₁.natDegree * g₂.natDegree + f₂.natDegree * g₁.natDegree + 1 ∧"),
    ("Level0", "      (-D.f'.nextCoeff - D.f'.natDegree * m) * (-D.g.nextCoeff - D.g.natDegree * m') +", "      (D.f'.nextCoeff - D.f'.natDegree * m) * (-D.g.nextCoeff - D.g.natDegree * m') +"),
    ("Level0", "    finrank ℂ (RI f g) = f.natDegree * g.natDegree ∧", "    finrank ℂ (RI f g) = f.natDegree + g.natDegree ∧"),
    ("TraceFormula", "theorem card_S : (S a b).card = finrank ℂ A := by", "theorem card_S : (S a b).card = finrank ℂ A + 1 := by"),
    ("Fibre", "      (LinearMap.trace ℂ[X] S (Algebra.lmul ℂ[X] S x)).eval c := by", "      (LinearMap.trace ℂ[X] S (Algebra.lmul ℂ[X] S x)).eval (c + 1) := by"),
    ("GrowthGen", "(hn : 2 ≤ f.natDegree) (hn' : 0 < f'.natDegree) (hg : IsCoprime g' g) (R₀ : ℝ) :", "(hn : 1 ≤ f.natDegree) (hn' : 0 < f'.natDegree) (hg : IsCoprime g' g) (R₀ : ℝ) :"),
    ("CaseII", "      g₁.natDegree * f₂.natDegree + g₂.natDegree * f₁.natDegree - 2 := by", "      g₁.natDegree * f₂.natDegree + g₂.natDegree * f₁.natDegree - 3 := by"),
    ("CaseIIb", "(h : ∀ t : ℝ, 0 < t → t < δ → t ^ p ≤ C * t ^ q) : q ≤ p := by", "(h : ∀ t : ℝ, 0 < t → t < δ → t ^ p ≤ C * t ^ q) : q < p := by"),
    ("CaseIIb", "    f₁ ^ f₂.natDegree = f₂ ^ f₁.natDegree := by\n  classical", "    f₁ ^ f₁.natDegree = f₂ ^ f₂.natDegree := by\n  classical"),
    ("Integral", "    (hg : IsCoprime g g')\n", "    (hg : IsCoprime g g)\n"),
    ("Constancy", "    (τ D φ).eval c = (τ D φ).eval 0 := by", "    (τ D φ).eval c = (τ D φ).eval 1 := by"),
    ("ResTop", "    M.det.coeff (∑ j, d j - 1) = (∑ j, e j) * (Matrix.of fun i j => (M i j).coeff (d j)).det := by",
     "    M.det.coeff (∑ j, d j - 1) = (Matrix.of fun i j => (M i j).coeff (d j)).det := by"),
]


def compiles(path: pathlib.Path) -> bool:
    r = subprocess.run(["timeout", "600", "nice", "-n", "10", "lake", "env", "lean", str(path)],
                       cwd=ROOT, capture_output=True, text=True)
    return r.returncode == 0 and "error" not in r.stdout


def main() -> int:
    bad = 0
    for name, old, new in MUTANTS:
        f = DIR / f"{name}.lean"
        src = f.read_text()
        if src.count(old) != 1:
            print(f"SETUP FAIL {name}: pattern count {src.count(old)}: {old[:60]!r}")
            bad += 1
            continue
        try:
            f.write_text(src.replace(old, new))
            ok = compiles(f)
        finally:
            f.write_text(src)
        print(f"{'SURVIVED' if ok else 'rejected'}  {name}: {new[:70]!r}")
        bad += ok
    print(f"{len(MUTANTS) - bad}/{len(MUTANTS)} rejected")
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
