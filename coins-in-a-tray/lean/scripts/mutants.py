#!/usr/bin/env python3
"""Mutation tests for LeanProofs/CoinsTray (coins in a tray, MO 513668): every wrong
variant must FAIL to check.

Each mutant copies one file to CoinsTray/Mut.lean with a single textual change and compiles it
with `lake env lean` (single process, background QoS). Unmutated copies must pass (baseline).
"""
import os
import pathlib
import signal
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
D = ROOT / "LeanProofs" / "CoinsTray"
MUT = D / "Mut.lean"

MUTANTS = [
    ("law of cosines with 1/d", "Basic.lean",
     "      1 - 2 / ((j - 1) * (k - 1)) := by", "      1 - 1 / ((j - 1) * (k - 1)) := by"),
    ("cos formula for 0 < d", "Basic.lean",
     "lemma cos_alpha (d : ℝ) (hd : 1 ≤ d) :", "lemma cos_alpha (d : ℝ) (hd : 0 < d) :"),
    ("rational rim angle for d = 3", "Basic.lean",
     "(∃ r : ℚ, alpha d = r * π) ↔ d = 1 ∨ d = 2 ∨ d = 4 := by",
     "(∃ r : ℚ, alpha d = r * π) ↔ d = 1 ∨ d = 2 ∨ d = 3 := by"),
    ("d = 1 left out", "Basic.lean",
     "(∃ r : ℚ, alpha d = r * π) ↔ d = 1 ∨ d = 2 ∨ d = 4 := by",
     "(∃ r : ℚ, alpha d = r * π) ↔ d = 2 ∨ d = 4 := by"),
    ("d = 4 irrational", "Basic.lean",
     "(hd : d ∈ ({6, 8, 12, 16} : Finset ℕ))", "(hd : d ∈ ({4, 8, 12, 16} : Finset ℕ))"),
    ("ring closes with alpha 8", "Basic.lean",
     "theorem dan_four : 2 * alpha 3 + alpha 9 = π := by", "theorem dan_four : 2 * alpha 3 + alpha 8 = π := by"),
    ("halves closer than 3/4", "Basic.lean",
     "      1 / 2 + 1 / 2 := by", "      1 / 2 + 1 / 4 := by"),
    ("root quadruple (-1, 2, 3, 3)", "Basic.lean",
     "    b = 2 ∧ c = 2 ∧ d = 3 := by", "    b = 2 ∧ c = 3 ∧ d = 3 := by"),
    ("root condition dropped", "Basic.lean",
     "(hcd : c ≤ d) (hroot : d ≤ -1 + b + c)", "(hcd : c ≤ d) (hroot : d ≤ 2 * b + 2 * c)"),
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
