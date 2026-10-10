#!/usr/bin/env python3
"""Mutation tests for LeanProofs/WindowSeq (a sequence that looks back half way): every wrong
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
D = ROOT / "LeanProofs" / "WindowSeq"
MUT = D / "Mut.lean"

MUTANTS = [
    ("recurrence divides by n + 1", "Seq.lean",
     "else a (k + 1) - a ((k + 1) / 2) / (k + 2)\n\n/-- The window",
     "else a (k + 1) - a ((k + 1) / 2) / (k + 3)\n\n/-- The window"),
    ("window starts at n/2 rounded down", "Seq.lean",
     "def W (n : ℕ) : Finset ℕ := Ico ((n + 1) / 2) n", "def W (n : ℕ) : Finset ℕ := Ico (n / 2) n"),
    ("weights shifted by one harmonic term", "Harm.lean",
     "    s n = (harmonic (n - 1) : ℝ) - harmonic ((n + 1) / 2 - 1) := by",
     "    s n = (harmonic (n - 1) : ℝ) - harmonic ((n + 1) / 2) := by"),
    ("eventually s n <= 2/3 (below log 2)", "Limit.lean",
     "lemma eventually_s_le : ∀ᶠ n in atTop, s n ≤ 3 / 4 :=",
     "lemma eventually_s_le : ∀ᶠ n in atTop, s n ≤ 2 / 3 :="),
    ("contraction with q <= 1", "Limit.lean",
     "theorem tendsto_zero_of_contract (e δ : ℕ → ℝ) (M q : ℝ) (hq0 : 0 ≤ q) (hq : q < 1)",
     "theorem tendsto_zero_of_contract (e δ : ℕ → ℝ) (M q : ℝ) (hq0 : 0 ≤ q) (hq : q ≤ 1)"),
    ("limit 1/(1 - log 3)", "Limit.lean",
     "theorem tendsto_c : Tendsto (fun n : ℕ => (n : ℝ) * a n) atTop (𝓝 (1 / (1 - log 2))) := by",
     "theorem tendsto_c : Tendsto (fun n : ℕ => (n : ℝ) * a n) atTop (𝓝 (1 / (1 - log 3))) := by"),
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
