#!/usr/bin/env python3
"""Mutation tests for LeanProofs/PairwiseAveraging.lean ("Five numbers, many averages", MO 421671):
every wrong variant must FAIL to check.

Each mutant copies the file to LeanProofs/PairwiseAveragingMut.lean with a single textual change and compiles it
with `lake env lean` (single process, nice 15). The unmutated copy must pass (baseline).
"""
import pathlib
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
SRC = ROOT / "LeanProofs" / "PairwiseAveraging.lean"
MUT = ROOT / "LeanProofs" / "PairwiseAveragingMut.lean"

MUTANTS = [
    ("lower bound k + 4", "    (hR : ∀ a, seq (B k) mv R a = t k) : k + 3 ≤ R := by", "    (hR : ∀ a, seq (B k) mv R a = t k) : k + 4 ≤ R := by"),
    ("upper bound in k + 2 moves", "theorem upper_bound (k : ℕ) (hk : 1 ≤ k) : ∀ a, seq (B k) (strategy k) (k + 3) a = t k := by",
     "theorem upper_bound (k : ℕ) (hk : 1 ≤ k) : ∀ a, seq (B k) (strategy k) (k + 2) a = t k := by"),
    ("tuple with 3t/2", "def B (k : ℕ) : Fin 5 → ℚ := ![2, -3, 1, 5 * t k / 2, 5 * t k / 2]", "def B (k : ℕ) : Fin 5 → ℚ := ![2, -3, 1, 3 * t k / 2, 5 * t k / 2]"),
    ("t = (1/2)^k", "def t (k : ℕ) : ℚ := (-1 / 2) ^ k", "def t (k : ℕ) : ℚ := (1 / 2) ^ k"),
    ("congruence up to r = k", "theorem no_congruence {k r q : ℕ} (hr : r < k)", "theorem no_congruence {k r q : ℕ} (hr : r ≤ k)"),
    ("count never n - 2", "    (hits u μ).card ≠ n - 1 := by", "    (hits u μ).card ≠ n - 2 := by"),
    ("a move adds one hit", "(hits (avg u p) μ).card = (hits u μ).card + 2 := by", "(hits (avg u p) μ).card = (hits u μ).card + 1 := by"),
    ("weights sum to 2^(r+1)", "    ∃ m : Fin n → ℕ, ∑ i, m i = 2 ^ r ∧", "    ∃ m : Fin n → ℕ, ∑ i, m i = 2 ^ (r + 1) ∧"),
    ("no balanced subset for k = 1", "theorem no_balanced_subset (k : ℕ) (hk : 2 ≤ k)", "theorem no_balanced_subset (k : ℕ) (hk : 1 ≤ k)"),
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
