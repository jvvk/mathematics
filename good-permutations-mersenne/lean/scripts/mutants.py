#!/usr/bin/env python3
"""Mutation tests for LeanProofs/GoodPerm (good permutations, MO 514690): every wrong
variant must FAIL to check.

Each mutant copies one file to WindowSeq/Mut.lean with a single textual change and compiles it
with `lake env lean` (single process, background QoS). Unmutated copies must pass (baseline).
"""
import os
import pathlib
import signal
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
D = ROOT / "LeanProofs" / "GoodPerm"
MUT = D / "Mut.lean"

MUTANTS = [
    ("asker's permutation with the sign of (-1)^t flipped", "Construction.lean",
     "def c (n t : ℕ) : ℤ := if t = 1 then 1 else (n : ℤ) + 2 - t - (-1) ^ t",
     "def c (n t : ℕ) : ℤ := if t = 1 then 1 else (n : ℤ) + 2 - t + (-1) ^ t"),
    ("interior lemma for blocks starting at position 1", "Construction.lean",
     "theorem interior (n t L : ℕ) (ht : 2 ≤ t)", "theorem interior (n t L : ℕ) (ht : 1 ≤ t)"),
    ("bad prefixes: length divides 2^m instead of 2^m - 1", "Construction.lean",
     "    (L : ℤ) ∣ S (c (2 ^ m - 1)) t L ↔ t = 1 ∧ L ∣ 2 ^ m - 1 := by",
     "    (L : ℤ) ∣ S (c (2 ^ m - 1)) t L ↔ t = 1 ∧ L ∣ 2 ^ m := by"),
    ("even prefixes up to length 2^(m+1)", "Construction.lean",
     "lemma prefix_even_not_dvd (m r : ℕ) (hL : 2 * r + 2 ≤ 2 ^ m - 1) :",
     "lemma prefix_even_not_dvd (m r : ℕ) (hL : 2 * r + 2 ≤ 2 ^ (m + 1)) :"),
    ("good iff prime from m = 1 (n = 1)", "Construction.lean",
     "theorem good_iff_prime (m : ℕ) (hm : 2 ≤ m)", "theorem good_iff_prime (m : ℕ) (hm : 1 ≤ m)"),
    ("permutation for every n, not only odd n", "Construction.lean",
     "theorem c_perm (n : ℕ) (hn : Odd n) : IsPerm n (c n) := by\n  obtain ⟨k, rfl⟩ := hn",
     "theorem c_perm (n : ℕ) : IsPerm n (c n) := by\n  obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' n"),
    ("block of length 2^(j+1) sums to 2^(j+1) times an odd number", "Mersenne.lean",
     "(hend : t + 2 ^ (j + 1) ≤ n + 1) : ∃ o : ℤ, Odd o ∧ S a t (2 ^ (j + 1)) = 2 ^ j * o := by",
     "(hend : t + 2 ^ (j + 1) ≤ n + 1) : ∃ o : ℤ, Odd o ∧ S a t (2 ^ (j + 1)) = 2 ^ (j + 1) * o := by"),
    ("middle block sums to (q - s) n / 2", "Mersenne.lean",
     "theorem middle_sum : 2 * S a (s + 1) (q - s) = ((q : ℤ) - s) * (n + 1) := by",
     "theorem middle_sum : 2 * S a (s + 1) (q - s) = ((q : ℤ) - s) * n := by"),
    ("Mersenne lengths for even n too", "Mersenne.lean",
     "theorem mersenne (hp : IsPerm n a) (hg : Good n a) (hodd : Odd n) (h3 : 3 ≤ n) :",
     "theorem mersenne (hp : IsPerm n a) (hg : Good n a) (hodd : 0 < n) (h3 : 3 ≤ n) :"),
    ("the middle value is q + 1", "Mersenne.lean",
     "    a (2 ^ (m - 1)) = 2 ^ (m - 1) ∧ ∀ i, 1 ≤ i → i < 2 ^ (m - 1) →",
     "    a (2 ^ (m - 1)) = 2 ^ (m - 1) + 1 ∧ ∀ i, 1 ≤ i → i < 2 ^ (m - 1) →"),
]


def check(text: str) -> bool:
    MUT.write_text(text)
    p = subprocess.Popen(["taskpolicy", "-c", "background", "lake", "env", "lean", str(MUT)], cwd=ROOT,
                         stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True,
                         start_new_session=True)
    try:
        out, _ = p.communicate(timeout=1200)
    except subprocess.TimeoutExpired:
        os.killpg(p.pid, signal.SIGKILL)  # lake's lean child too
        p.communicate()
        print("  (timed out: counted as not compiling)", flush=True)
        return False
    return p.returncode == 0 and "error" not in out


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
