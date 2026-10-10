#!/usr/bin/env python3
"""Mutation tests for LeanProofs/TaxicabEleven (every taxicab distance once, MSE 4967838): every wrong
variant must FAIL to check.

Each mutant copies one file to TaxicabEleven/Mut.lean with a single textual change and compiles it
with `lake env lean` (single process, background QoS). Unmutated copies must pass (baseline).
"""
import os
import pathlib
import signal
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
D = ROOT / "LeanProofs" / "TaxicabEleven"
MUT = D / "Mut.lean"

MUTANTS = [
    ("N/2 odd numbers", "Basic.lean",
     "((Icc (1 : ℤ) N).filter Odd).card = (N + 1) / 2 := by",
     "((Icc (1 : ℤ) N).filter Odd).card = N / 2 := by"),
    ("cross pairs a * a", "Basic.lean",
     "      (univ.filter c).card * (univ.filter fun i => ¬ c i).card := by",
     "      (univ.filter c).card * (univ.filter c).card := by"),
    ("N even iff n = 0, 3 mod 4", "Basic.lean",
     "lemma choose_two_even_iff (n : ℕ) : n * (n - 1) / 2 % 2 = 0 ↔ n % 4 = 0 ∨ n % 4 = 1 := by",
     "lemma choose_two_even_iff (n : ℕ) : n * (n - 1) / 2 % 2 = 0 ↔ n % 4 = 0 ∨ n % 4 = 3 := by"),
    ("parity without the factor 2", "Basic.lean",
     "      n - 2 * ((n * (n - 1) / 2 % 2 : ℕ) : ℤ) := by",
     "      n - ((n * (n - 1) / 2 % 2 : ℕ) : ℤ) := by"),
    ("n - 1 a square", "Basic.lean",
     "(n % 4 = 2 ∨ n % 4 = 3 → IsSquare (n - 2))", "(n % 4 = 2 ∨ n % 4 = 3 → IsSquare (n - 1))"),
    ("point A moved", "Basic.lean", "  ![(0, 14), (0, 16),", "  ![(0, 15), (0, 16),"),
    ("eleven realises 54", "Basic.lean",
     "theorem eleven : Realises eleven_pts 55 := by", "theorem eleven : Realises eleven_pts 54 := by"),
    ("colour split 6, 5", "Basic.lean",
     "    (univ.filter fun i => colour (eleven_pts i)).card = 7 ∧",
     "    (univ.filter fun i => colour (eleven_pts i)).card = 6 ∧"),
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
