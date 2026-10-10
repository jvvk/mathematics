#!/usr/bin/env python3
"""Mutation tests for LeanProofs/InversePairs (inverse pairs, MSE 5146740): every wrong
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
D = ROOT / "LeanProofs" / "InversePairs"
MUT = D / "Mut.lean"

MUTANTS = [
    ("orthogonality sums to p - 1", "Rect.lean",
     "ψ p (u * b) = if b = 0 then (p : ℂ) else 0 := by",
     "ψ p (u * b) = if b = 0 then (p : ℂ) - 1 else 0 := by"),
    ("K(0,0) = p", "Rect.lean",
     "lemma K_zero_zero : K p 0 0 = p - 1 := by", "lemma K_zero_zero : K p 0 0 = p := by"),
    ("main term |I||J|/(p - 1)", "Rect.lean",
     "    (N p I J : ℂ) = (#I * #J : ℂ) / p + (1 / (p : ℂ) ^ 2) *",
     "    (N p I J : ℂ) = (#I * #J : ℂ) / (p - 1) + (1 / (p : ℂ) ^ 2) *"),
    ("sine bound with p/4", "Rect.lean",
     "    1 / |Real.sin (Real.pi * k / p)| ≤ (p / 2) * (1 / (k : ℝ) + 1 / ((p : ℝ) - k)) := by",
     "    1 / |Real.sin (Real.pi * k / p)| ≤ (p / 4) * (1 / (k : ℝ) + 1 / ((p : ℝ) - k)) := by"),
    ("divisor bound with eps = 0 allowed", "Div.lean",
     "theorem divisor_bound (ε : ℝ) (hε : 0 < ε) :", "theorem divisor_bound (ε : ℝ) (hε : 0 ≤ ε) :"),
    ("products 1 + kp from k = 2", "Bound.lean",
     "    R p m ≤ ∑ k ∈ Icc 1 (m / p), #(1 + k * p).divisors := by",
     "    R p m ≤ ∑ k ∈ Icc 2 (m / p), #(1 + k * p).divisors := by"),
    ("layer-cake boundary term with the wrong sign", "Bound.lean",
     "      - w ((p - 1) ^ 2 + 1) / p := by", "      + w ((p - 1) ^ 2 + 1) / p := by"),
    ("sum of 1/sqrt a at least 2 sqrt p", "Sums.lean",
     "    2 * (Real.sqrt p - 1) ≤ ∑ a ∈ Ico 1 p, w a ∧",
     "    2 * Real.sqrt p ≤ ∑ a ∈ Ico 1 p, w a ∧"),
    ("full grid within 1/sqrt p of 4", "Sums.lean",
     "|(∑ a ∈ Ico 1 p, w a) ^ 2 / p - 4| ≤ 8 / Real.sqrt p := by",
     "|(∑ a ∈ Ico 1 p, w a) ^ 2 / p - 4| ≤ 1 / Real.sqrt p := by"),
    ("limit 4", "Limit.lean",
     "      have : Fact p.1.Prime := ⟨p.2⟩; S p.1) atTop (𝓝 5) := by",
     "      have : Fact p.1.Prime := ⟨p.2⟩; S p.1) atTop (𝓝 4) := by"),
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
