#!/usr/bin/env python3
"""Mutation tests for LeanProofs/StanleySylow (MO 489315): every wrong variant must FAIL to check.

Each mutant copies one file to StanleySylow/Mut.lean with a single textual change and compiles it
with `lake env lean` (single process, nice 15). Unmutated copies must pass (baseline).
"""
import os
import pathlib
import signal
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
D = ROOT / "LeanProofs" / "StanleySylow"
MUT = D / "Mut.lean"

MUTANTS = [
    ("Sylow recurrence adds |G| one index late (the printed slip)", "Sylow.lean",
     "Ps n * (Ps n + C (a n))", "Ps n * (Ps n + C (a (n+1)))"),
    ("factor A: constant c_(n+1) -> 2 c_(n+1)", "Sylow.lean",
     "def AS (n : ℕ) : ℤ[X] := Ps (n+1) - C (2*a n) * Ps n + C (a (n+1))",
     "def AS (n : ℕ) : ℤ[X] := Ps (n+1) - C (2*a n) * Ps n + C (2*a (n+1))"),
    ("mod 5: c_1 = 2 -> 3", "Sylow.lean",
     "have ha : reduce5 (a 1) = 2 := by norm_num [a, reduce5]",
     "have ha : reduce5 (a 1) = 3 := by norm_num [a, reduce5]"),
    ("top coefficients: 2^n < i -> 2^n <= i", "Sylow.lean",
     "(hi : 2 ^ n < i) : (AS n).coeff i", "(hi : 2 ^ n ≤ i) : (AS n).coeff i"),
    ("critical value of the tower: 3 -> 2", "Sylow.lean",
     "(h3 : ¬ IsSquare (H.eval 3))", "(h3 : ¬ IsSquare (H.eval 2))"),
    ("non-square: 2 -> 4", "Question.lean",
     "theorem ns_two : ¬ IsSquare (2 : F5) := by decide", "theorem ns_two : ¬ IsSquare (4 : F5) := by decide"),
    ("c_k mod 5 = 3 -> 2", "Question.lean",
     "theorem a_mod5 (k : ℕ) : reduce5 (a (k+2)) = 3 := by", "theorem a_mod5 (k : ℕ) : reduce5 (a (k+2)) = 2 := by"),
    ("1/4 in F_5: 4 -> 2", "Question.lean",
     "theorem inv_four : (4 : F5)⁻¹ = 4 := by", "theorem inv_four : (4 : F5)⁻¹ = 2 := by"),
    ("c_(n+1) = 2 c_n^2 -> 2 c_n", "Question.lean",
     "| n+1 => 2 * a n ^ 2", "| n+1 => 2 * a n"),
]


def check(text: str) -> bool:
    MUT.write_text(text)
    p = subprocess.Popen(["nice", "-n", "15", "lake", "env", "lean", str(MUT)], cwd=ROOT,
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
