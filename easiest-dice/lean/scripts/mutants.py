#!/usr/bin/env python3
"""Mutation tests for LeanProofs/CappedDice.lean ("Capped dice", MSE 5149864):
every wrong variant must FAIL to check.

Each mutant copies the file to LeanProofs/CappedDiceMut.lean with a single textual change and compiles it
with `lake env lean` (single process, nice 15). The unmutated copy must pass (baseline).
"""
import pathlib
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
SRC = ROOT / "LeanProofs" / "CappedDice.lean"
MUT = ROOT / "LeanProofs" / "CappedDiceMut.lean"

MUTANTS = [
    ("no cap on face probabilities", "def Adm {k : ℕ} (r : ℝ) (p : Fin k → ℝ) : Prop := (∀ i, 0 ≤ p i ∧ p i ≤ r) ∧ ∑ i, p i = 1",
     "def Adm {k : ℕ} (r : ℝ) (p : Fin k → ℝ) : Prop := (∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1"),
    ("q bound one face too generous", "    ∃ a ≤ k, g p q u v ≤ u * min 1 (a * r) - v * max 0 (1 - (k - a) * r) := by",
     "    ∃ a ≤ k, g p q u v ≤ u * min 1 (a * r) - v * max 0 (1 - (k - a - 1) * r) := by"),
    ("staircase sum off by one", "theorem stair_sum {r : ℝ} (hr : 0 ≤ r) (a : ℕ) : ∑ i ∈ range a, stair r i = min 1 (a * r) := by",
     "theorem stair_sum {r : ℝ} (hr : 0 ≤ r) (a : ℕ) : ∑ i ∈ range a, stair r i = min 1 ((a + 1) * r) := by"),
    ("q* not reversed", "noncomputable def qstar (k : ℕ) (r : ℝ) : Fin k → ℝ := fun i => stair r (k - 1 - i)",
     "noncomputable def qstar (k : ℕ) (r : ℝ) : Fin k → ℝ := fun i => stair r i"),
    ("staircase admissible without k r >= 1", "theorem pstar_adm {k : ℕ} {r : ℝ} (hr : 0 ≤ r) (hk : 1 ≤ k * r) : Adm r (pstar k r) := by",
     "theorem pstar_adm {k : ℕ} {r : ℝ} (hr : 0 ≤ r) (hk : 0 ≤ k * r) : Adm r (pstar k r) := by"),
    ("domination reversed", "    (hq : Adm r q) {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) : g p q u v ≤ g (pstar k r) (qstar k r) u v := by",
     "    (hq : Adm r q) {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) : g (pstar k r) (qstar k r) u v ≤ g p q u v := by"),
    ("overlap uses rate 2", "    overlap D = 1 - G D 1 1 := by", "    overlap D = 1 - G D 1 2 := by"),
    ("staircase overlap is the largest", "    overlap (fun _ : Fin n => (pstar k r, qstar k r)) ≤ overlap D :=",
     "    overlap D ≤ overlap (fun _ : Fin n => (pstar k r, qstar k r)) :="),
    ("asker range widened to r > 1/4", "theorem asker_optimal {r : ℝ} (h1 : 1 / 3 < r)", "theorem asker_optimal {r : ℝ} (h1 : 1 / 4 < r)"),
    ("asker pair with faces moved", "def pA (r : ℝ) : Fin 4 → ℝ := ![r, 1 - 2 * r, r, 0]", "def pA (r : ℝ) : Fin 4 → ℝ := ![r, r, 1 - 2 * r, 0]"),
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
