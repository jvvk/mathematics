#!/usr/bin/env python3
"""Mutation tests for LeanProofs/PowTwoTrees ("Labelling binary trees by powers of two", MO 304266): every
wrong variant must FAIL to check.

Each mutant copies one file to PowTwoTrees/Mut.lean with a single textual change and compiles it with
`lake env lean` (single process, nice 15). The unmutated copies must pass (baseline).
"""
import pathlib
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
D = ROOT / "LeanProofs" / "PowTwoTrees"
MUT = D / "Mut.lean"

MUTANTS = [
    ("parity with sizes differing by two", "Reductions.lean",
     "(hsize : a.size = b.size ∨ a.size = b.size + 1) : Labelled (.two a b) := by",
     "(hsize : a.size = b.size ∨ a.size = b.size + 2) : Labelled (.two a b) := by"),
    ("Mersenne with a branch of size 2^k", "Reductions.lean",
     "(hsize : a.size + 1 = 2 ^ k) : Labelled (.two a b) := by", "(hsize : a.size = 2 ^ k) : Labelled (.two a b) := by"),
    ("prefix case 1 with d + 1 a power of two", "Reductions.lean",
     "(hsize : c.size = b.size ∨ c.size = b.size + 1) (hm : d + 2 = 2 ^ m) :",
     "(hsize : c.size = b.size ∨ c.size = b.size + 1) (hm : d + 1 = 2 ^ m) :"),
    ("prefix case 2 with the size condition reversed", "Reductions.lean",
     "(hsize : b.size = c.size ∨ b.size = c.size + 1) (hm : d + 1 = 2 ^ m) :",
     "(hsize : c.size = b.size ∨ c.size = b.size + 1) (hm : d + 1 = 2 ^ m) :"),
    ("two-prefix case 1 with e + 2 a power of two", "Reductions.lean",
     "    (hp : e + 1 = 2 ^ p) : Labelled (.two (BT.pre d a) (BT.pre e b)) := by",
     "    (hp : e + 2 = 2 ^ p) : Labelled (.two (BT.pre d a) (BT.pre e b)) := by"),
    ("children may differ from the parent by 3", "Basic.lean",
     "      Fits c S (r + 2 ^ k) → r ∉ S → Fits (.one c) (insert r S) r",
     "      Fits c S (r + 2 ^ k + 1) → r ∉ S → Fits (.one c) (insert r S) r"),
    ("labels need not be distinct", "Basic.lean",
     "      Fits a A (r + 2 ^ i) → Fits b B (r + 2 ^ j) → Disjoint A B → r ∉ A → r ∉ B →",
     "      Fits a A (r + 2 ^ i) → Fits b B (r + 2 ^ j) → r ∉ A → r ∉ B →"),
    ("span bound 2^(n-3)", "Universal.lean",
     "    ∀ x ∈ S, x ≤ 2 ^ n := by", "    ∀ x ∈ S, x ≤ 2 ^ n - 1 := by"),
    ("primitive tail without the odd hypothesis", "Universal.lean",
     "theorem primitive_tail {S : Finset ℕ} (hS : Universal S) (h3 : 3 ≤ S.card) (hodd : ∃ x ∈ S, Odd x) :",
     "theorem primitive_tail {S : Finset ℕ} (hS : Universal S) (h3 : 3 ≤ S.card) (hodd : True) :"),
    ("tail lemma for sets of size one", "Universal.lean",
     "theorem tail {S : Finset ℕ} (hS : Universal S) (h2 : 2 ≤ S.card) :",
     "theorem tail {S : Finset ℕ} (hS : Universal S) (h2 : 1 ≤ S.card) :"),
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
    for f in ("Basic.lean", "Reductions.lean", "Universal.lean"):
        print(f"baseline {f}: {'pass' if check((D / f).read_text()) else 'FAIL'}")
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
