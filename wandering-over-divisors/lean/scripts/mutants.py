#!/usr/bin/env python3
"""Mutation tests for LeanProofs/DivisorWalk ("Wandering over the divisors of a power of ten", MO 363120):
every wrong variant must FAIL to check.

Each mutant copies one file to DivisorWalk/Mut.lean (module name adjusted) with a single textual change and
compiles it with `lake env lean` (single process, nice 15). The unmutated copies must pass (baseline).
"""
import pathlib
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
D = ROOT / "LeanProofs" / "DivisorWalk"
MUT = D / "Mut.lean"

MUTANTS = [
    ("Theorem 5 claimed for n = 1", "Theorems.lean",
     "theorem bottom (n a : ℕ) (hn : 2 ≤ n)", "theorem bottom (n a : ℕ) (hn : 1 ≤ n)"),
    ("(2,2) claimed for n = 2", "Theorems.lean",
     "theorem two_two (n : ℕ) (hn : 3 ≤ n)", "theorem two_two (n : ℕ) (hn : 2 ≤ n)"),
    ("Theorem 3 claimed at k = n", "Theorems.lean",
     "theorem diag (n k : ℕ) (hk : k < n)", "theorem diag (n k : ℕ) (hk : k ≤ n)"),
    ("corner (n,0) claimed for n = 1", "Theorems.lean",
     "theorem corner_right (n : ℕ) (hn : 2 ≤ n)", "theorem corner_right (n : ℕ) (hn : 1 ≤ n)"),
    ("Theorem 3 with the D opening", "Theorems.lean",
     "(hq : q = (k + 1, k) ∨ q = (k, k + 1))", "(hq : q = (k + 1, k) ∨ q = (k - 1, k - 1))"),
    ("Theorem 5: Bob answers N instead of D", "Theorems.lean",
     "  refine ⟨(a - 1, 0), ⟨by simp; omega, by simp, Or.inr (Or.inr ⟨by simp; omega, by simp, by simp⟩)⟩, ?_, ?_⟩",
     "  refine ⟨(a, 2), ⟨by simp; omega, by simp; omega, Or.inr (Or.inl rfl)⟩, ?_, ?_⟩"),
    ("Lemma 2 without the stopping condition", "Game.lean",
     "      (m = 0 ∨ (n - 1, m - 1) ∈ V) → BobWins n V (n, y) := by",
     "      True → BobWins n V (n, y) := by"),
    ("D move allowed from the bottom row", "Game.lean",
     "(1 ≤ p.1 ∧ 1 ≤ p.2 ∧ q = (p.1 - 1, p.2 - 1))", "(1 ≤ p.1 ∧ q = (p.1 - 1, p.2 - 1))"),
    ("a fourth move W added", "Game.lean",
     "    (q = (p.1 + 1, p.2) ∨ q = (p.1, p.2 + 1) ∨",
     "    (q = (p.1 + 1, p.2) ∨ q = (p.1 - 1, p.2) ∨ q = (p.1, p.2 + 1) ∨"),
    ("climb: Bob's square need not be free", "Game.lean",
     "      · exact (hF x y le_rfl le_rfl).2.2 h", "      · exact (hF x y le_rfl le_rfl).2.1 h"),
]


def check(text: str) -> bool:
    MUT.write_text(text)
    try:
        r = subprocess.run(["nice", "-n", "15", "lake", "env", "lean", str(MUT)], cwd=ROOT,
                           capture_output=True, text=True, timeout=900)
        return r.returncode == 0 and "error" not in r.stdout
    finally:
        MUT.unlink(missing_ok=True)


def main() -> int:
    ok = True
    for f in ("Game.lean", "Theorems.lean"):
        base = (D / f).read_text()
        if f == "Theorems.lean":
            base = base  # imports Game; unchanged copy must compile
        print(f"baseline {f}: {'pass' if check(base) else 'FAIL'}")
    for name, f, old, new in MUTANTS:
        src = (D / f).read_text()
        if old not in src:
            print(f"SKIP (pattern missing): {name}")
            ok = False
            continue
        passed = check(src.replace(old, new, 1))
        print(f"{'SURVIVED' if passed else 'rejected'}  {name}")
        ok &= not passed
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
