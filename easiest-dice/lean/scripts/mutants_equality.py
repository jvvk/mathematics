#!/usr/bin/env python3
"""Mutation tests for LeanProofs/CappedDiceEquality.lean ("Capped dice", MSE 5149864, equality cases):
every wrong variant must FAIL to check.

Each mutant copies the file to LeanProofs/CappedDiceEqualityMut.lean with a single textual change and compiles it
with `lake env lean` (single process, nice 15). The unmutated copy must pass (baseline).
"""
import pathlib
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
SRC = ROOT / "LeanProofs" / "CappedDiceEquality.lean"
MUT = ROOT / "LeanProofs" / "CappedDiceEqualityMut.lean"

MUTANTS = [
    ("uniqueness already at n = 2", "    (n : ℕ) (hn : 3 ≤ n) (h : overlap (fun _ : Fin n => (p, q)) = overlap (S 4 r n)) : Relabel r p q := by",
     "    (n : ℕ) (hn : 2 ≤ n) (h : overlap (fun _ : Fin n => (p, q)) = overlap (S 4 r n)) : Relabel r p q := by"),
    ("relabelled face (r, s) read as (r, r)", "    p a = r ∧ q a = 0 ∧ p b = r ∧ q b = 1 - 2 * r ∧ p c = 1 - 2 * r ∧ q c = r ∧ p d = 0 ∧ q d = r",
     "    p a = r ∧ q a = 0 ∧ p b = r ∧ q b = r ∧ p c = 1 - 2 * r ∧ q c = r ∧ p d = 0 ∧ q d = r"),
    ("face (r, 0) from a low rate", "    {u v : ℝ} (hu : 0 < u) (hv : 0 < v) (huv : u * r < v * (1 - 2 * r))",
     "    {u v : ℝ} (hu : 0 < u) (hv : 0 < v) (huv : v * (1 - 2 * r) < u * r)"),
    ("n = 1 condition min = 0", "    overlap (fun _ : Fin 1 => (p, q)) = overlap (S 4 r 1) ↔ ∀ i, max (p i) (q i) = r := by",
     "    overlap (fun _ : Fin 1 => (p, q)) = overlap (S 4 r 1) ↔ ∀ i, min (p i) (q i) = 0 := by"),
    ("family x up to r", "theorem equality_two_family (h1 : 1 / 3 < r) (h2 : r < 1 / 2) {x : ℝ} (hx0 : 0 ≤ x) (hxs : x ≤ 1 - 2 * r) :",
     "theorem equality_two_family (h1 : 1 / 3 < r) (h2 : r < 1 / 2) {x : ℝ} (hx0 : 0 ≤ x) (hxs : x ≤ r) :"),
    ("tightness with v = 0 allowed", "    {u v : ℝ} (hu : 0 < u) (hv : 0 < v) (h : g p q u v = g (pstar k r) (qstar k r) u v) :\n    ∑ i ∈ pos p q u v, p i",
     "    {u v : ℝ} (hu : 0 < u) (hv : 0 ≤ v) (h : g p q u v = g (pstar k r) (qstar k r) u v) :\n    ∑ i ∈ pos p q u v, p i"),
    ("rate gap from one roll", "theorem rate_gap (h1 : 1 / 3 < r) (h2 : r < 1 / 2) {m : ℕ} (hm : 2 ≤ m) :",
     "theorem rate_gap (h1 : 1 / 3 < r) (h2 : r < 1 / 2) {m : ℕ} (hm : 1 ≤ m) :"),
    ("pin at rate zero", "    {i0 j0 : Fin 4} (hi0 : p i0 = r ∧ q i0 = 0) (hj0 : p j0 = 0 ∧ q j0 = r) {c : ℝ} (hc : 0 < c)\n    (h : g p q c c",
     "    {i0 j0 : Fin 4} (hi0 : p i0 = r ∧ q i0 = 0) (hj0 : p j0 = 0 ∧ q j0 = r) {c : ℝ} (hc : 0 ≤ c)\n    (h : g p q c c"),
    ("family excess at (x, r) off by x", "      g (pF r x) (qF r) x r = x * r ∧ g (pF r x) (qF r) (1 - 2 * r - x) r = (1 - 2 * r - x) * r := by",
     "      g (pF r x) (qF r) x r = x * r + x ∧ g (pF r x) (qF r) (1 - 2 * r - x) r = (1 - 2 * r - x) * r := by"),
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
