#!/usr/bin/env python3
"""Mutation tests for LeanProofs/TangentCircles (MO 498968): every wrong variant must FAIL to check.

Each mutant copies one file to TangentCircles/Mut.lean with a single textual change and compiles it
with `lake env lean` (single process, nice 15). Unmutated copies must pass (baseline).
"""
import pathlib
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
D = ROOT / "LeanProofs" / "TangentCircles"
MUT = D / "Mut.lean"

MUTANTS = [
    ("half-chord A: wrong sign of 2p", "Chords.lean",
     "      a ^ 2 * Real.cos ω * Real.cos (ω - 2 * p) := by", "      a ^ 2 * Real.cos ω * Real.cos (ω + 2 * p) := by"),
    ("half-chord B: wrong sign of 2q", "Chords.lean",
     "      b ^ 2 * Real.cos ω * Real.cos (ω + 2 * q) := by", "      b ^ 2 * Real.cos ω * Real.cos (ω - 2 * q) := by"),
    ("midpoints: sum has sin term", "Chords.lean",
     "      (a + b) * Real.cos ω := by\n  ring", "      (a + b) * Real.cos ω + z * Real.sin ω := by\n  ring"),
    ("product: plus sin squared", "Chords.lean",
     "      Real.cos (p + q) ^ 2 - Real.sin η ^ 2 := by", "      Real.cos (p + q) ^ 2 + Real.sin η ^ 2 := by"),
    ("tidy: swapped weights", "Chords.lean",
     "      b * Real.cos p ^ 2 + a * Real.cos q ^ 2 := by", "      a * Real.cos p ^ 2 + b * Real.cos q ^ 2 := by"),
    ("integral: 2 pi", "Integral.lean",
     "theorem integral_g : ∫ η in -(π / 2 - |s|)..(π / 2 - |s|), g s η = π := by",
     "theorem integral_g : ∫ η in -(π / 2 - |s|)..(π / 2 - |s|), g s η = 2 * π := by"),
    ("integral: derivative without the square root", "Integral.lean",
     "noncomputable def g (s η : ℝ) : ℝ := Real.cos η / Real.sqrt (Real.cos s ^ 2 - Real.sin η ^ 2)",
     "noncomputable def g (s η : ℝ) : ℝ := Real.cos η / (Real.cos s ^ 2 - Real.sin η ^ 2)"),
    ("density: Cauchy(a) only", "Crossing.lean",
     "noncomputable def f (a b z : ℝ) : ℝ := (1 / π) * (a / (a ^ 2 + z ^ 2) + b / (b ^ 2 + z ^ 2))",
     "noncomputable def f (a b z : ℝ) : ℝ := (1 / π) * (2 * a / (a ^ 2 + z ^ 2))"),
    ("half mass: pi/3", "Crossing.lean",
     "    Real.arctan (Real.sqrt (a * b) / a) + Real.arctan (Real.sqrt (a * b) / b) = π / 2 := by",
     "    Real.arctan (Real.sqrt (a * b) / a) + Real.arctan (Real.sqrt (a * b) / b) = π / 3 := by"),
    ("half: 2/3", "Crossing.lean",
     "    ∫ z in (0 : ℝ)..Real.sqrt (a * b), f a b z = 1 / 2 := by",
     "    ∫ z in (0 : ℝ)..Real.sqrt (a * b), f a b z = 2 / 3 := by"),
    ("tail: wrong sign", "Crossing.lean",
     "      1 / 2 - (Real.arctan (r / a) + Real.arctan (r / b)) / π := by\n  rw [integral_f",
     "      1 / 2 + (Real.arctan (r / a) + Real.arctan (r / b)) / π := by\n  rw [integral_f"),
    ("density form: cos(p+q)", "Crossing.lean",
     "    (a + b) * Real.cos p * Real.cos q * Real.cos (p - q) / (a * b) =\n      a / (a ^ 2 + z ^ 2)",
     "    (a + b) * Real.cos p * Real.cos q * Real.cos (p + q) / (a * b) =\n      a / (a ^ 2 + z ^ 2)"),
    ("incircle: Heron with a + b", "Incircle.lean",
     "  (hheron : ρ ^ 2 * (a + b + c) = a * b * c)", "  (hheron : ρ ^ 2 * (a + b) = a * b * c)"),
    ("incircle: half-angles sum to pi", "Incircle.lean",
     "    Real.arctan (ρ / a) + Real.arctan (ρ / b) + Real.arctan (ρ / c) = π / 2 := by",
     "    Real.arctan (ρ / a) + Real.arctan (ρ / b) + Real.arctan (ρ / c) = π := by"),
    ("incircle: total miss 1/3", "Incircle.lean",
     "    (1 / 2 - (Real.arctan (ρ / c) + Real.arctan (ρ / a)) / π) = 1 / 2 := by",
     "    (1 / 2 - (Real.arctan (ρ / c) + Real.arctan (ρ / a)) / π) = 1 / 3 := by"),
    ("sphere: fold without the factor 2", "Sphere.lean",
     "Real.cos (d + -η) / Real.cos (-η) = 2 * Real.cos d := by",
     "Real.cos (d + -η) / Real.cos (-η) = Real.cos d := by"),
    ("sphere: lune of width pi - C", "Sphere.lean",
     "lemma lune {s α β γ : ℝ} (h : α + β + γ = π / 2) : α + β < s ↔ π - 2 * γ < 2 * s := by",
     "lemma lune {s α β γ : ℝ} (h : α + β + γ = π / 2) : α + β < s ↔ 2 * γ < 2 * s := by"),
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
