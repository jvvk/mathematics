#!/usr/bin/env python3
"""Mutation tests for LeanProofs/NominoParity.lean (n-omino rectangles, MO 378923):
every wrong variant must FAIL to check.

Each mutant copies the file to LeanProofs/NominoParityMut.lean with a single textual change and compiles it
with `lake env lean` (single process, nice 15). The unmutated copy must pass (baseline).
"""
import pathlib
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
SRC = ROOT / "LeanProofs" / "NominoParity.lean"
MUT = ROOT / "LeanProofs" / "NominoParityMut.lean"

MUTANTS = [
    ("colour ignores y", "def chi (p : Cell) : ℤ := if (p.1 + p.2) % 2 = 0 then 1 else -1",
     "def chi (p : Cell) : ℤ := if p.1 % 2 = 0 then 1 else -1"),
    ("a symmetry that shears", "  let q : Cell := if k.val / 4 = 1 then (p.2, p.1) else p",
     "  let q : Cell := if k.val / 4 = 1 then (p.2, p.1 + p.2) else p"),
    ("odd rectangles balanced", "theorem imb_rect_even {a b : ℕ} (h : Even a ∨ Even b) : imb (rect a b) = 0 := by",
     "theorem imb_rect_even {a b : ℕ} (h : Even a ∨ Odd b) : imb (rect a b) = 0 := by"),
    ("odd pieces allowed", "theorem no_rectangle {N : ℕ} (P : Fin N → Finset Cell) (heven : ∀ i, Even (P i).card)",
     "theorem no_rectangle {N : ℕ} (P : Fin N → Finset Cell) (heven : ∀ i, 0 < (P i).card)"),
    ("sum = 0 mod 4 also obstructs", "    (hsum : (∑ i, (imb (P i)).natAbs) % 4 = 2) (a b : ℕ) (k : Fin N → Fin 8) (t : Fin N → Cell) :",
     "    (hsum : (∑ i, (imb (P i)).natAbs) % 4 ≠ 1) (a b : ℕ) (k : Fin N → Fin 8) (t : Fin N → Cell) :"),
    ("n = 12 with 59248", "      (n = 16 ∧ ∑ i, (imb (P i)).natAbs = 13329078))",
     "      (n = 12 ∧ ∑ i, (imb (P i)).natAbs = 59248))"),
    ("imbalance parity off by one", "theorem imb_mod_two (S : Finset Cell) : imb S % 2 = (S.card : ℤ) % 2 := by",
     "theorem imb_mod_two (S : Finset Cell) : imb S % 2 = (S.card + 1 : ℤ) % 2 := by"),
    ("tiles may overlap", "  (Set.PairwiseDisjoint ((univ : Finset (Fin N)) : Set (Fin N)) fun i => (P i).image (place (k i) (t i))) ∧\n",
     "  True ∧\n"),
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
