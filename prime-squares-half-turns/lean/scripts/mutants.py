#!/usr/bin/env python3
"""Mutation tests for LeanProofs/PrimeSquares.lean ("Prime squares and half-turns", MO 487157):
every wrong variant must FAIL to check.

Each mutant copies the file to LeanProofs/PrimeSquaresMut.lean with a single textual change and compiles it
with `lake env lean` (single process, nice 15). The unmutated copy must pass (baseline).
"""
import pathlib
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
SRC = ROOT / "LeanProofs" / "PrimeSquares.lean"
MUT = ROOT / "LeanProofs" / "PrimeSquaresMut.lean"

MUTANTS = [
    ("oddness dropped", "(hodd : p ≠ 2)", "(hodd : True)"),
    ("sigma not an involution", "(hσσ : ∀ a, σ (σ a) = a)", "(hσσ : True)"),
    ("evaluation not sigma-invariant", "(hε : ∀ a, ε (σ a) = ε a)", "(hε : True)"),
    ("both primes divide F", "    q₁ ∣ F ∨ q₂ ∣ F := by\n  have hF0", "    q₁ ∣ F ∧ q₂ ∣ F := by\n  have hF0"),
    ("unused orientation not forced to vanish", "(hU0 : u = 0 → U = 0)", "(hU0 : True)"),
    ("row degree allowed to reach p", "    (hdeg : f.natDegree < p) (hdvd", "    (hdeg : f.natDegree ≤ p) (hdvd"),
    ("2p cells", "    (hcount : ∑ k ∈ Finset.range (F.natDegree + 1), (F.coeff k).eval 1 = p)",
     "    (hcount : ∑ k ∈ Finset.range (F.natDegree + 1), (F.coeff k).eval 1 = 2 * p)"),
    ("Q_p(1) = p + 1", "theorem cyclotomic_prime_eval_one {p : ℕ} (hp : p.Prime) : (cyclotomic p ℤ).eval 1 = p := by",
     "theorem cyclotomic_prime_eval_one {p : ℕ} (hp : p.Prime) : (cyclotomic p ℤ).eval 1 = p + 1 := by"),
    ("coefficients in {0, 2}", "(h01 : ∀ i, f.coeff i = 0 ∨ f.coeff i = 1)", "(h01 : ∀ i, f.coeff i = 0 ∨ f.coeff i = 2)"),
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
