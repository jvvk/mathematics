#!/usr/bin/env python3
"""Mutation tests for LeanProofs/ProductTrajectory/*.lean (Physics SE 816017, product trajectories):
every wrong variant must FAIL to check.

Each mutant copies one module to <Module>Mut.lean in the same folder with a single textual change and
compiles it with `lake env lean` (single process, nice 15). The unmutated copies must pass (baseline).
Dependencies are the built oleans of the unmutated modules.
"""

import pathlib
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
DIR = ROOT / "LeanProofs" / "ProductTrajectory"

# (module, name, old, new)
MUTANTS = [
    (
        "Graded",
        "drop q ≠ 0 (q = 0 makes every product homogeneous)",
        "    (hp : p ≠ 0) (hq : q ≠ 0)\n    {m : ℤ}",
        "    (hp : p ≠ 0)\n    {m : ℤ}",
    ),
    (
        "Graded",
        "top weights add to m + 1",
        "    a + b = m := by",
        "    a + b = m + 1 := by",
    ),
    (
        "RankOne",
        "vacuous minor hypothesis",
        "(h : ∀ i i' l l', F i l * F i' l' = F i l' * F i' l)",
        "(h : ∀ i i' l l', F i l * F i' l' = F i l * F i' l')",
    ),
    (
        "Core",
        "v-weight 2 instead of 1",
        "(fun i => if i = j then 1 else 0)",
        "(fun i => if i = j then 2 else 0)",
    ),
    (
        "Core",
        "core without orthogonality of coefficient matrices",
        "(horth : ∀ s s', s ≠ s' → ∑ i, ∑ l, star ((F i l).coeff s) * (F i l).coeff s' = 0)",
        "(horth : ∀ s s', s = s' → ∑ i, ∑ l, star ((F i l).coeff s) * (F i l).coeff s' = 0)",
    ),
    (
        "Core",
        "coefficient of U p * V q without conjugation",
        "(U p * V q).coeff (sumElim μ ν) = star (p.coeff μ) * q.coeff ν",
        "(U p * V q).coeff (sumElim μ ν) = p.coeff μ * q.coeff ν",
    ),
    (
        "Characters",
        "torus evaluation with the wrong sign of the phase",
        "eval (zt ω t) (monomial r a) = a * exp (-(I * (dot ω r * t)))",
        "eval (zt ω t) (monomial r a) = a * exp (I * (dot ω r * t))",
    ),
    (
        "Characters",
        "frequency lattice without the shift c",
        "LinearIndependent ℤ ω ∧ ∀ j, lam j = dot ω (e j) + c",
        "LinearIndependent ℤ ω ∧ ∀ j, lam j = dot ω (e j)",
    ),
    (
        "Characters",
        "dot injective without independence",
        "theorem dot_injective (ω : Fin k → ℝ) (hω : LinearIndependent ℤ ω) :",
        "theorem dot_injective (ω : Fin k → ℝ) (hω : True) :",
    ),
    (
        "Main",
        "main without the product hypothesis (only at t = 0)",
        "(hprod : ∀ t : ℝ, ∃ (a : ι → ℂ) (b : κ → ℂ),\n      ∑ j, exp (-(I * (lam j * t))) • v j = vecMulVec a b)",
        "(hprod : ∀ t : ℝ, t = 0 → ∃ (a : ι → ℂ) (b : κ → ℂ),\n      ∑ j, exp (-(I * (lam j * t))) • v j = vecMulVec a b)",
    ),
    (
        "Main",
        "main without orthogonality of the components",
        "(horth : ∀ j j', j ≠ j' → ∑ i, ∑ l, star (v j i l) * v j' i l = 0)",
        "(horth : ∀ j j', j = j' → ∑ i, ∑ l, star (v j i l) * v j' i l = 0)",
    ),
    (
        "Main",
        "claim the A-factor coefficients are zero (diagonal instead of off-diagonal)",
        "      (∀ μ ν, μ ≠ ν → ∑ i, star (x μ i) * x ν i = 0) ∧",
        "      (∀ μ ν, μ = ν → ∑ i, star (x μ i) * x ν i = 0) ∧",
    ),
    ("Heisenberg", "determinant claimed to be 2", "theorem det_M (t : ℝ) : (Mt t).det = 1 := by",
     "theorem det_M (t : ℝ) : (Mt t).det = 2 := by"),
    ("Heisenberg", "norm claimed to be 5", "theorem normSq_M (t : ℝ) : ∑ i, ∑ j, normSq (Mt t i j) = 6 := by",
     "theorem normSq_M (t : ℝ) : ∑ i, ∑ j, normSq (Mt t i j) = 5 := by"),
    ("Heisenberg", "trajectory entry sign flipped (1 - i z^2)", "!![-zz t, 1 + I * zz t ^ 2; I * zz t ^ 2 - 1, zz t ^ 3]",
     "!![-zz t, 1 - I * zz t ^ 2; I * zz t ^ 2 - 1, zz t ^ 3]"),
    ("Heisenberg", "singlet component replaced by the triplet", "  | 0 => !![0, 1; -1, 0]", "  | 0 => !![0, 1; 1, 0]"),
    ("Heisenberg", "frequency lemma without nonzero coefficients", "    (hd : ∀ ν ∈ Nν, d ν ≠ 0)\n    (h : ∀ t : ℝ, ∑ ν ∈ Nν,",
     "    (h : ∀ t : ℝ, ∑ ν ∈ Nν,"),
    ("Heisenberg", "non-locality without Hermitian C",
     "theorem not_local : ¬ ∃ A C : Matrix (Fin 2) (Fin 2) ℂ, A.IsHermitian ∧ C.IsHermitian ∧",
     "theorem not_local : ¬ ∃ A C : Matrix (Fin 2) (Fin 2) ℂ, A.IsHermitian ∧"),
    ("SO4", "so(4) split with a wrong coefficient", "(((ω 0 3 + ω 1 2) / 2 : ℝ) : ℂ) • σx", "(((ω 0 3 + ω 1 2) / 3 : ℝ) : ℂ) • σx"),
    ("SO4", "tau_fixed without the determinant hypothesis", "(hXX : X * Xᴴ = r • 1) (hdet : X.det = r) :", "(hXX : X * Xᴴ = r • 1) :"),
    ("SO4", "quaternion structure with a wrong sign", "def tau (X : M2) : M2 := !![star (X 1 1), -star (X 1 0); -star (X 0 1), star (X 0 0)]",
     "def tau (X : M2) : M2 := !![star (X 1 1), star (X 1 0); -star (X 0 1), star (X 0 0)]"),
    ("ExpSums", "constant modulus without nonzero coefficients", "theorem const_modulus_single (S : Finset ℝ) (c : ℝ → ℂ) (hc : ∀ s ∈ S, c s ≠ 0) (hS : S.Nonempty)",
     "theorem const_modulus_single (S : Finset ℝ) (c : ℝ → ℂ) (hS : S.Nonempty)"),
    ("ExpSums", "coefficient uniqueness claims c = -d", "(h : ∀ t : ℝ, ∑ s ∈ S, c s * ch s t = ∑ s ∈ S, d s * ch s t) : ∀ s ∈ S, c s = d s := by",
     "(h : ∀ t : ℝ, ∑ s ∈ S, c s * ch s t = ∑ s ∈ S, d s * ch s t) : ∀ s ∈ S, c s = -d s := by"),
    ("MaxEnt", "maxent without orthogonality", "theorem maxent (S : Finset ℝ) (W : ℝ → M2) (hW : ∀ s ∈ S, W s ≠ 0)\n    (horth : ∀ s ∈ S, ∀ s' ∈ S, s ≠ s' → ip (W s) (W s') = 0)\n    (hmax",
     "theorem maxent (S : Finset ℝ) (W : ℝ → M2) (hW : ∀ s ∈ S, W s ≠ 0)\n    (hmax"),
    ("MaxEnt", "maxent without maximal entanglement", "    (hmax : ∀ t : ℝ, ∃ r : ℂ, Nt S W t * (Nt S W t)ᴴ = r • 1) :", "    :"),
    ("MaxEnt", "generator with pairing s -> kappa + s", "    (hpair : ∀ s ∈ S, κ - s ∈ S ∧ tau (W (κ - s)) = W s) :",
     "    (hpair : ∀ s ∈ S, κ + s ∈ S ∧ tau (W (κ + s)) = W s) :"),
]


def check(module: str, text: str) -> bool:
    mut = DIR / f"{module}Mut.lean"
    mut.write_text(text)
    try:
        r = subprocess.run(
            ["nice", "-n", "15", "lake", "env", "lean", str(mut)],
            cwd=ROOT,
            capture_output=True,
            text=True,
            timeout=1200,
        )
    finally:
        mut.unlink(missing_ok=True)
    return r.returncode == 0 and "error" not in r.stdout


def main() -> int:
    bad = 0
    for module in sorted({m for m, *_ in MUTANTS}):
        if not check(module, (DIR / f"{module}.lean").read_text()):
            print(f"BASELINE FAILS: {module}")
            return 1
    print("baseline: passes")
    for module, name, old, new in MUTANTS:
        src = (DIR / f"{module}.lean").read_text()
        if src.count(old) != 1:
            print(f"SETUP ERROR ({src.count(old)} matches): {module}: {name}")
            bad += 1
            continue
        ok = check(module, src.replace(old, new))
        print(f"{'SURVIVED' if ok else 'rejected'}: {module}: {name}")
        bad += ok
    print(f"{len(MUTANTS) - bad}/{len(MUTANTS)} mutants rejected")
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
