#!/usr/bin/env python3
"""Mutation tests for LeanProofs/PowerTwoMatching (every other residue, MSE 2060312): every wrong
variant must FAIL to check.

Each mutant copies one file to PowerTwoMatching/Mut.lean with a single textual change and compiles it
with `lake env lean` (single process, background QoS). Unmutated copies must pass (baseline).
"""
import os
import pathlib
import signal
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
D = ROOT / "LeanProofs" / "PowerTwoMatching"
MUT = D / "Mut.lean"

MUTANTS = [
    ("parity count ignores B", "Basic.lean",
     "def par (k : ℕ) (e f : ℕ → ℕ) : ℕ := (∑ r ∈ range (2 ^ k), (e r + f r)) % 2",
     "def par (k : ℕ) (e f : ℕ → ℕ) : ℕ := (∑ r ∈ range (2 ^ k), (e r)) % 2"),
    ("sums distinct modulo 2^k", "Basic.lean",
     "    Set.InjOn (fun r => (elt k e r + elt k f (σ r)) % 2 ^ (k + 1)) (range (2 ^ k)) ∧",
     "    Set.InjOn (fun r => (elt k e r + elt k f (σ r)) % 2 ^ k) (range (2 ^ k)) ∧"),
    ("matching of parity 1 - p", "Basic.lean",
     "theorem exists_matching (k : ℕ) (e f : ℕ → ℕ) : ∃ σ, Good k e f σ (par k e f) := by",
     "theorem exists_matching (k : ℕ) (e f : ℕ → ℕ) : ∃ σ, Good k e f σ (1 - par k e f) := by"),
    ("forced parity 1 - p", "Basic.lean",
     "    q = par k e f := by", "    q = 1 - par k e f := by"),
    ("parity class sums to n(n-1) + q", "Basic.lean",
     "∑ t ∈ (range (2 * n)).filter (fun t => t % 2 = q), t = n * (n - 1) + q * n := by",
     "∑ t ∈ (range (2 * n)).filter (fun t => t % 2 = q), t = n * (n - 1) + q := by"),
    ("parity class has n + 1 elements", "Basic.lean",
     "    ((range (2 * n)).filter (fun t => t % 2 = q)).card = n := by",
     "    ((range (2 * n)).filter (fun t => t % 2 = q)).card = n + 1 := by"),
    ("halving modulo 2^(k+2)", "Basic.lean",
     "    (2 * x) % 2 ^ (k + 2) = (2 * y) % 2 ^ (k + 2) ↔ x % 2 ^ (k + 1) = y % 2 ^ (k + 1) := by",
     "    (2 * x) % 2 ^ (k + 2) = (2 * y) % 2 ^ (k + 2) ↔ x % 2 ^ (k + 2) = y % 2 ^ (k + 2) := by"),
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
