#!/usr/bin/env python3
"""Mutation tests for LeanProofs/DeletionCover.lean ("Sixteen words", MO 142857):
every wrong variant must FAIL to check.

Each mutant copies the file to LeanProofs/DeletionCoverMut.lean with a single textual change and compiles it
with `lake env lean` (single process, nice 15). The unmutated copy must pass (baseline).
"""
import pathlib
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
SRC = ROOT / "LeanProofs" / "DeletionCover.lean"
MUT = ROOT / "LeanProofs" / "DeletionCoverMut.lean"

MUTANTS = [
    ("blocks cover one more letter", "    Covers (cat S T) (n₁ + n₂) := by", "    Covers (cat S T) (n₁ + n₂ + 1) := by"),
    ("block count additive", "theorem card_append_le (S T : Finset (List Bool)) : (cat S T).card ≤ S.card * T.card :=", "theorem card_append_le (S T : Finset (List Bool)) : (cat S T).card ≤ S.card + T.card :="),
    ("k-fold cover of size k c", "∃ T : Finset (List Bool), Covers T (k * n) ∧ Uniform T (k * m) ∧ T.card ≤ S.card ^ k := by", "∃ T : Finset (List Bool), Covers T (k * n) ∧ Uniform T (k * m) ∧ T.card ≤ k * S.card := by"),
    ("H additive", "    H (n₁ + n₂) (b₁ + b₂) ≤ H n₁ b₁ * H n₂ b₂ := by", "    H (n₁ + n₂) (b₁ + b₂) ≤ H n₁ b₁ + H n₂ b₂ := by"),
    ("H at least 2", "theorem H_pos (n b : ℕ) : 0 < H n b := by", "theorem H_pos (n b : ℕ) : 1 < H n b := by"),
    ("alpha below 15^(1/15)", "    Real.exp (subadditive_log.lim / 3) ≤ (16 : ℝ) ^ ((1 : ℝ) / 15) := by", "    Real.exp (subadditive_log.lim / 3) ≤ (15 : ℝ) ^ ((1 : ℝ) / 15) := by"),
    ("16^(1/15) above 1.2031", "theorem rate_16 : (1.2030 : ℝ) < (16 : ℝ) ^ ((1 : ℝ) / 15) ∧", "theorem rate_16 : (1.2031 : ℝ) < (16 : ℝ) ^ ((1 : ℝ) / 15) ∧"),
    ("17^(1/15) above 1.2080", "theorem rate_17 : (1.2078 : ℝ) < (17 : ℝ) ^ ((1 : ℝ) / 15) := by", "theorem rate_17 : (1.2080 : ℝ) < (17 : ℝ) ^ ((1 : ℝ) / 15) := by"),
    ("words one letter longer", "theorem mem_words {m : ℕ} {y : List Bool} : y ∈ words m ↔ y.length = m := by", "theorem mem_words {m : ℕ} {y : List Bool} : y ∈ words m ↔ y.length = m + 1 := by"),
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
