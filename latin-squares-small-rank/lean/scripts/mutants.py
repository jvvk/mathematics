#!/usr/bin/env python3
"""Mutation tests for LeanProofs/LatinRank (Latin squares of small rank): every wrong
variant must FAIL to check.

Each mutant copies one file to LatinRank/Mut.lean with a single textual change and compiles it
with `lake env lean` (single process, background QoS). Unmutated copies must pass (baseline).
"""
import os
import pathlib
import signal
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
D = ROOT / "LeanProofs" / "LatinRank"
MUT = D / "Mut.lean"

MUTANTS = [
    ("factorisation: sum of |x_i|^2 = d + 1", "Factor.lean",
     "      ∑ i, ‖x i‖ ^ 2 = finrank ℝ K ∧", "      ∑ i, ‖x i‖ ^ 2 = finrank ℝ K + 1 ∧"),
    ("centred squares sum n(n^2-1)/2", "Bound.lean",
     "    ∑ k : Fin n, (2 * ((k : ℕ) : ℝ) - (n - 1)) ^ 2 = (n : ℝ) * ((n : ℝ) ^ 2 - 1) / 3 := by",
     "    ∑ k : Fin n, (2 * ((k : ℕ) : ℝ) - (n - 1)) ^ 2 = (n : ℝ) * ((n : ℝ) ^ 2 - 1) / 2 := by"),
    ("bound with 4(n-1)", "Bound.lean",
     "    3 * ((n : ℝ) - 1) ≤ (n + 1) * finrank ℝ (K L) := by",
     "    4 * ((n : ℝ) - 1) ≤ (n + 1) * finrank ℝ (K L) := by"),
    ("strictness for even n", "Bound.lean",
     "theorem rank_bound_strict (hn : 3 ≤ n) (hodd : Odd n) (hL : IsLatin L) :",
     "theorem rank_bound_strict (hn : 3 ≤ n) (hodd : Even n) (hL : IsLatin L) :"),
    ("rank 4 already at n = 4", "Bound.lean",
     "theorem four_le_rank (hn : 5 ≤ n) (hL : IsLatin L) : 4 ≤ (V L).rank := by",
     "theorem four_le_rank (hn : 4 ≤ n) (hL : IsLatin L) : 4 ≤ (V L).rank := by"),
    ("rank 5 for n >= 5", "Bound.lean",
     "theorem four_le_rank (hn : 5 ≤ n) (hL : IsLatin L) : 4 ≤ (V L).rank := by",
     "theorem four_le_rank (hn : 5 ≤ n) (hL : IsLatin L) : 5 ≤ (V L).rank := by"),
    ("order-6 witness with two symbols swapped", "Witness.lean",
     "def L6 : Matrix (Fin 6) (Fin 6) (Fin 6) := !![0, 5, 1, 4, 2, 3;",
     "def L6 : Matrix (Fin 6) (Fin 6) (Fin 6) := !![5, 0, 1, 4, 2, 3;"),
    ("XOR factor with a wrong sign", "Witness.lean",
     "def Y4 : Matrix (Fin 3) (Fin 4) ℤ := !![1, 2, 3, 4; 1, -1, 1, -1; 2, 2, -2, -2]",
     "def Y4 : Matrix (Fin 3) (Fin 4) ℤ := !![1, 2, 3, 4; 1, 1, 1, -1; 2, 2, -2, -2]"),
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
