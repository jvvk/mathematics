#!/usr/bin/env python3
"""Mutation tests for LeanProofs/DiscCover (critical random discs, MO 458793): every wrong
variant must FAIL to check.

Each mutant copies one file to DiscCover/Mut.lean with a single textual change and compiles it
with `lake env lean` (single process, background QoS). Unmutated copies must pass (baseline).
"""
import os
import pathlib
import signal
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
D = ROOT / "LeanProofs" / "DiscCover"
MUT = D / "Mut.lean"

MUTANTS = [
    ("lens ball radius 1 - s/4", "Basic.lean", "Metric.ball ((1 / 2 : ℝ) • z) (1 - ‖z‖ / 2) ⊆", "Metric.ball ((1 / 2 : ℝ) • z) (1 - ‖z‖ / 4) ⊆"),
    ("lens bound 1 - s/4", "Basic.lean", "theorem lens_sq (s : ℝ) : 1 - s ≤", "theorem lens_sq (s : ℝ) : 1 - s / 4 ≤"),
    ("sum of 1/sqrt n <= sqrt N", "Basic.lean", "1 / √(n : ℝ) ≤ 2 * √(N : ℝ) := by", "1 / √(n : ℝ) ≤ √(N : ℝ) := by"),
    ("H >= 3 log(1/t) - C", "Basic.lean", "    2 * log (1 / t) - log π - 2 ≤", "    3 * log (1 / t) - log π - 2 ≤"),
    ("1/t not integrable on [1, 2]", "Basic.lean", "(fun t : ℝ => t⁻¹) MeasureTheory.volume 0 1", "(fun t : ℝ => t⁻¹) MeasureTheory.volume 1 2"),
    ("sliver x^2/2", "Basic.lean", "1 - √(1 - x ^ 2) ≤ x ^ 2 := by", "1 - √(1 - x ^ 2) ≤ x ^ 2 / 2 := by"),
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
