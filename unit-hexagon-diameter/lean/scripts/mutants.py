#!/usr/bin/env python3
"""Mutation tests for LeanProofs/UnitHexagon (MO 481323): every wrong variant must FAIL to check.

Each mutant copies one file to UnitHexagon/Mut.lean with a single textual change and compiles it
with `lake env lean` (single process, nice 15). Unmutated copies must pass (baseline).
"""
import pathlib
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
D = ROOT / "LeanProofs" / "UnitHexagon"
MUT = D / "Mut.lean"

MUTANTS = [
    ("turns: weaker hypothesis 2a+b <= pi+1", "Turns.lean",
     "(h1 : 2 * α + β ≤ π) (h2 : α + 2 * β ≤ π) :\n    ∃ s x",
     "(h1 : 2 * α + β ≤ π + 1) (h2 : α + 2 * β ≤ π) :\n    ∃ s x"),
    ("turns: max angle > 2pi/5", "Turns.lean", "π / 2 < α + β ∧ π / 3 < max α β",
     "π / 2 < α + β ∧ 2 * π / 5 < max α β"),
    ("projection: sqrt 3 instead of sqrt 2", "Projection.lean",
     "(h02 : ‖X₀ - X₂‖ ≤ Real.sqrt 2) (h31 : X₃ ≠ X₁) (h10 : X₀ ≠ X₁)\n    {w₀",
     "(h02 : ‖X₀ - X₂‖ ≤ Real.sqrt 3) (h31 : X₃ ≠ X₁) (h10 : X₀ ≠ X₁)\n    {w₀"),
    ("four-hull: wrong sign in K", "FourHull.lean",
     "      Real.sin γ - Real.sin (β + γ) + Real.sin (α + β + γ) := by\n  set S",
     "      Real.sin γ + Real.sin (β + γ) + Real.sin (α + β + γ) := by\n  set S"),
    ("four-hull: factor 2 instead of 4", "FourHull.lean",
     "      4 * Real.sin (γ / 2) * Real.cos ((β + γ) / 2) * Real.cos (γ + β / 2) := by\n  have h1",
     "      2 * Real.sin (γ / 2) * Real.cos ((β + γ) / 2) * Real.cos (γ + β / 2) := by\n  have h1"),
    ("four-hull: wrong outer-angle order", "FourHull.lean",
     "(hb' : β ≤ π / 2) (hc' : γ ≤ π / 2) (hS : π < α + β + γ) (hca : γ ≤ α) :",
     "(hb' : β ≤ π / 2) (hc' : γ ≤ π / 2) (hS : π < α + β + γ) (hca : α ≤ γ) :"),
    ("four-hull: S > 3pi/2", "FourHull.lean",
     "(h0 : 0 ≤ t₀) (h4 : 0 ≤ t₄) (hne : ¬ (t₀ = 0 ∧ t₄ = 0)) : π < α + β + γ",
     "(h0 : 0 ≤ t₀) (h4 : 0 ≤ t₄) (hne : ¬ (t₀ = 0 ∧ t₄ = 0)) : 3 * π / 2 < α + β + γ"),
    ("triangle: apex included in the median bound", "Triangle.lean",
     "lemma median_lt_one {y₀ x y : ℝ} (hy₀ : 0 ≤ y₀) (hy₀h : y₀ < h)",
     "lemma median_lt_one {y₀ x y : ℝ} (hy₀ : 0 ≤ y₀) (hy₀h : y₀ ≤ h)"),
    ("triangle: unit neighbour of Z off the base", "Triangle.lean",
     "    y = 0 ∧ (x = a ∨ x = -a) := by", "    y = h ∧ (x = a ∨ x = -a) := by"),
    ("triangle: cosine rule bound 2", "Triangle.lean",
     "(hd : 2 - 2 * Real.cos θ ≤ 1) :", "(hd : 2 - 2 * Real.cos θ ≤ 2) :"),
    ("triangle: turns need not alternate", "Triangle.lean",
     "theorem invariant_along_path (left convex : ℕ → Prop) (k : ℕ)\n    (hl : ∀ i < k, (left (i + 1) ↔ ¬ left i)) (hc : ∀ i < k, (convex (i + 1) ↔ ¬ convex i)) :",
     "theorem invariant_along_path (left convex : ℕ → Prop) (k : ℕ)\n    (hl : ∀ i < k, (left (i + 1) ↔ ¬ left i)) (hc : ∀ i < k, (convex (i + 1) ↔ convex i)) :"),
    ("pocket: r > 2k/3", "Counting.lean", "(hC : ∀ i ∈ C, 3 * π / 2 ≤ φ i) : 3 * C.card < 2 * k",
     "(hC : ∀ i ∈ C, 3 * π / 2 ≤ φ i) : 3 * C.card < k"),
    ("hexagon: exactly two reflex", "Counting.lean",
     "(hsum : ∑ i, ι i = 4 * π) : R.card = 1 ∨ R.card = 2", "(hsum : ∑ i, ι i = 4 * π) : R.card = 2"),
    ("octagon: exactly two reflex", "Counting.lean",
     "(hsum : ∑ i, ι i = 6 * π) : R.card = 2 ∨ R.card = 3", "(hsum : ∑ i, ι i = 6 * π) : R.card = 2"),
    ("rays: wrong weight in the triangle turn", "Rays.lean",
     "cross (F - E) (A - F) = -μ * orient A C E ∧", "cross (F - E) (A - F) = -ν * orient A C E ∧"),
    ("rays: d need not be inside the hull", "Rays.lean",
     "(hfd : 0 < cross f d) (heb : 0 < cross e b) (hed : 0 < cross e d) :",
     "(hfd : 0 < cross f d) (heb : 0 < cross e b) (hed : 0 < cross e b) :"),
    ("sharp: sign identity with 3t", "Sharpness.lean",
     "2 * Ey t - r2 t = 16 * t * (1 - 2 * t) / (5 * (1 + t ^ 2))",
     "2 * Ey t - r2 t = 16 * t * (1 - 3 * t) / (5 * (1 + t ^ 2))"),
    ("sharp: D off the unit circle about C", "Sharpness.lean",
     "def Dx (t : ℝ) : ℝ := 2 * t ^ 2 / (1 + t ^ 2)", "def Dx (t : ℝ) : ℝ := 3 * t ^ 2 / (1 + t ^ 2)"),
    ("sharp: limit k = 1", "Sharpness.lean", "lemma kk_zero : kk 0 = 3 / 2 := by", "lemma kk_zero : kk 0 = 1 := by"),
    ("sharp: E convex", "Sharpness.lean",
     "    cross (V t 4 - V t 3) (V t 5 - V t 4) < 0 ∧", "    0 < cross (V t 4 - V t 3) (V t 5 - V t 4) ∧"),
    ("sharp: diameter limit below 2", "Sharpness.lean",
     "    (∀ i j, d2 (V t i) (V t j) < 2 + ε) ∧", "    (∀ i j, d2 (V t i) (V t j) < 3 / 2 + ε) ∧"),
]


def check(text: str) -> bool:
    MUT.write_text(text)
    r = subprocess.run(["nice", "-n", "15", "lake", "env", "lean", str(MUT)], cwd=ROOT,
                       capture_output=True, text=True, timeout=900)
    return r.returncode == 0 and "error" not in r.stdout


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
