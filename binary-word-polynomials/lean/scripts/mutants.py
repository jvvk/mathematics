#!/usr/bin/env python3
"""Mutation tests for LeanProofs/BlockReversal.lean (binary words with the same characteristic polynomial, MO 514920):
every wrong variant must FAIL to check.

Each mutant copies the file to LeanProofs/BlockReversalMut.lean with a single textual change and compiles it
with `lake env lean` (single process, nice 15). The unmutated copy must pass (baseline).
"""
import pathlib
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
SRC = ROOT / "LeanProofs" / "BlockReversal.lean"
MUT = ROOT / "LeanProofs" / "BlockReversalMut.lean"

MUTANTS = [
    ("factors swapped in the lemma", "    l' * (x ⬝ᵥ (Ms.prod *ᵥ y)) = l * (x' ⬝ᵥ (Ms.reverse.prod *ᵥ y')) := by",
     "    l * (x ⬝ᵥ (Ms.prod *ᵥ y)) = l' * (x' ⬝ᵥ (Ms.reverse.prod *ᵥ y')) := by"),
    ("G need not be symmetric", "theorem block_reversal (G : Matrix (Fin 2) (Fin 2) R) (hG : Gᵀ = G)",
     "theorem block_reversal (G : Matrix (Fin 2) (Fin 2) R) (hG : G = G)"),
    ("recurrence uses the wrong letter", "    P t (w ++ [c, d]) = (t - bv d) * P t (w ++ [c]) - P t w := by",
     "    P t (w ++ [c, d]) = (t - bv c) * P t (w ++ [c]) - P t w := by"),
    ("p - s on the diagonal", "  !![Z 0 0 - Z 1 1, Z 1 0 - Z 0 1; Z 1 0 - Z 0 1, Z 0 0 - Z 1 1]",
     "  !![Z 0 0 + Z 1 1, Z 1 0 - Z 0 1; Z 1 0 - Z 0 1, Z 0 0 + Z 1 1]"),
    ("eps sign flipped", "def eps (c : Bool) : R := if c then 1 else -1", "def eps (c : Bool) : R := if c then -1 else 1"),
    ("R with equal end letters", "    (hY : ∀ Y ∈ Ys, SameClass (M (X : ℤ[X]) Y) (M X (c :: (m ++ [!c])))) :",
     "    (hY : ∀ Y ∈ Ys, SameClass (M (X : ℤ[X]) Y) (M X (c :: (m ++ [c])))) :"),
    ("R context not flipped", "    P (X : ℤ[X]) ((!c) :: (m ++ [!c]) ++ Ys.flatten ++ (c :: (m ++ [c]))) =",
     "    P (X : ℤ[X]) (c :: (m ++ [!c]) ++ Ys.flatten ++ (c :: (m ++ [c]))) ="),
    ("interleaving G wrong sign", "  !![1 - Z 0 1 ^ 2, Z 0 1 * Z 0 0; Z 0 1 * Z 0 0, -Z 0 0 ^ 2]",
     "  !![1 + Z 0 1 ^ 2, Z 0 1 * Z 0 0; Z 0 1 * Z 0 0, -Z 0 0 ^ 2]"),
    ("interleaving blocks W a", "      P X (W ++ (as.map fun a => a :: W).reverse.flatten) := by",
     "      P X (W ++ (as.map fun a => W ++ [a]).reverse.flatten) := by"),
    ("complement without the sign", "theorem complement (t : R) (w : List Bool) : P t (w.map (!·)) = (-1) ^ w.length * P (1 - t) w := by",
     "theorem complement (t : R) (w : List Bool) : P t (w.map (!·)) = P (1 - t) w := by"),
    ("degree off by one", "    (M (X : ℤ[X]) w 0 0).Monic ∧ (M (X : ℤ[X]) w 0 0).natDegree = w.length ∧",
     "    (M (X : ℤ[X]) w 0 0).Monic ∧ (M (X : ℤ[X]) w 0 0).natDegree = w.length + 1 ∧"),
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
