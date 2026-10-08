#!/usr/bin/env python3
"""Mutation tests for LeanProofs/Spans (MO 442949): every wrong variant must FAIL to check.

Each mutant copies one file to Spans/Mut.lean with a single textual change and compiles it
with `lake env lean` (single process, nice 15). Unmutated copies must pass (baseline).
"""
import pathlib
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
D = ROOT / "LeanProofs" / "Spans"
MUT = D / "Mut.lean"

MUTANTS = [
    ("direction: one turn too many", "Basic.lean",
     "def θ (a : Fin m → ℝ) (i : ℕ) : ℝ := ∑ j ∈ range i, ext a j",
     "def θ (a : Fin m → ℝ) (i : ℕ) : ℝ := ∑ j ∈ range (i + 1), ext a j"),
    ("length swap: wrong sign", "Moves.lean",
     "Z (l ∘ Equiv.swap i j) a = Z l a + ((l j - l i : ℝ) : ℂ) * (e (θ a i) - e (θ a j))",
     "Z (l ∘ Equiv.swap i j) a = Z l a + ((l i - l j : ℝ) : ℂ) * (e (θ a i) - e (θ a j))"),
    ("rotation: moved segment in the wrong direction", "Moves.lean",
     "Z (l ∘ finRotate (m + 2)) (a ∘ finRotate (m + 1)) = Wtail l a + (l 0 : ℂ) * e (T a)",
     "Z (l ∘ finRotate (m + 2)) (a ∘ finRotate (m + 1)) = Wtail l a + (l 0 : ℂ) * e (ext a 0)"),
    ("resultant: arg < T/2", "Support.lean",
     "lemma arg_lt_T (hm : 1 ≤ m) : arg (Z l a) < T a", "lemma arg_lt_T (hm : 1 ≤ m) : arg (Z l a) < T a / 2"),
    ("turn exchange: wrong midpoint", "Exchange.lean",
     "(ext a k - ext a (k + 1)) * (θ a k + θ a (k + 2) - 2 * arg (Z l a)) < 0",
     "(ext a k - ext a (k + 1)) * (θ a k + θ a (k + 1) - 2 * arg (Z l a)) < 0"),
    ("endpoint lemma: drop a0", "Structure.lean",
     "theorem endpoint_arg : 2 * arg (Z l a) < T a + ext a 0", "theorem endpoint_arg : 2 * arg (Z l a) < T a"),
    ("half: T/2 -> 2T/3", "Structure.lean",
     "theorem half_lt_arg (h0 : l 0 < l (Fin.last m)) : T a / 2 < arg (Z l a)",
     "theorem half_lt_arg (h0 : l 0 < l (Fin.last m)) : 2 * T a / 3 < arg (Z l a)"),
    ("first turn ascends", "Structure.lean",
     "(h0 : l 0 < l (Fin.last m)) : ext a 1 < ext a 0", "(h0 : l 0 < l (Fin.last m)) : ext a 0 < ext a 1"),
    ("last turn descends", "Structure.lean", "    ext a (m - 1) < ext a m", "    ext a m < ext a (m - 1)"),
    ("pattern P1 with q = 102", "N4.lean",
     "  l 0 < l 3 ∧ l 3 < l 1 ∧ l 1 < l 2 ∧ a 1 < a 2 ∧ a 2 < a 0",
     "  l 0 < l 3 ∧ l 3 < l 1 ∧ l 1 < l 2 ∧ a 1 < a 0 ∧ a 0 < a 2"),
    ("pattern P3 replaced by the excluded (0321, 102)", "N4.lean",
     "  l 0 < l 3 ∧ l 3 < l 1 ∧ l 1 < l 2 ∧ a 1 < a 0 ∧ a 0 < a 2",
     "  l 0 < l 3 ∧ l 3 < l 2 ∧ l 2 < l 1 ∧ a 1 < a 0 ∧ a 0 < a 2"),
    ("witness value off by one", "Witness.lean", "= 12945800 / 143117", "= 12945801 / 143117"),
    ("witness 2 data changed", "Witness.lean",
     "def Ls2 : Fin 4 → ℝ := ![2, 3, 4, 5]", "def Ls2 : Fin 4 → ℝ := ![2, 3, 4, 6]"),
    ("half-angle formula: wrong cosine", "Witness.lean",
     "⟨(1 - x ^ 2) / (1 + x ^ 2), 2 * x / (1 + x ^ 2)⟩", "⟨(1 + x ^ 2) / (1 + x ^ 2), 2 * x / (1 + x ^ 2)⟩"),
]


def check(text: str) -> bool:
    MUT.write_text(text)
    r = subprocess.run(["nice", "-n", "15", "lake", "env", "lean", str(MUT)], cwd=ROOT,
                       capture_output=True, text=True, timeout=600)
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
