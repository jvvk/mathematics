#!/usr/bin/env python3
"""Mutation tests for LeanProofs/SandorYang (deleting the powers of four): every wrong
variant must FAIL to check.

Each mutant copies one file to SandorYang/Mut.lean with a single textual change and compiles it
with `lake env lean` (single process, background QoS). Unmutated copies must pass (baseline).
"""
import os
import pathlib
import signal
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
D = ROOT / "LeanProofs" / "SandorYang"
MUT = D / "Mut.lean"

MUTANTS = [
    ("identity with 2 U D instead of 3 U D", "Basic.lean",
     "      U ^ 2 - 3 * U * D E + 3 * D E ^ 2 - (1 - X) * D E ^ 3 := by",
     "      U ^ 2 - 2 * U * D E + 3 * D E ^ 2 - (1 - X) * D E ^ 3 := by"),
    ("bound without the m^2 term", "Basic.lean",
     "    ((n + 1 : ℕ) : ℤ) + 1 - 3 * m E (n + 1) - (m E (n + 1) : ℤ) ^ 2 ≤ R E 3 (n + 1) - R E 3 n := by",
     "    ((n + 1 : ℕ) : ℤ) + 1 - 3 * m E (n + 1) ≤ R E 3 (n + 1) - R E 3 n := by"),
    ("triples counted with c allowed in E", "Basic.lean",
     "(fun x => x.2.1 ∉ E ∧ x.2.2 ∉ E ∧ x.1.2 ∉ E)", "(fun x => x.2.1 ∉ E ∧ x.2.2 ∉ E)"),
    ("reduction without 0 in A", "Basic.lean",
     "theorem strictMono_of_three (h0 : 0 ∉ E) (h3", "theorem strictMono_of_three (h3"),
    ("delete the powers of two instead", "Powers.lean",
     "def E4 : Set ℕ := {e | ∃ j, e = 4 ^ (j + 2)}", "def E4 : Set ℕ := {e | ∃ j, e = 2 ^ (j + 2)}"),
    ("strict increase for h = 2", "Powers.lean",
     "theorem R_strictMono (h : ℕ) (hh : 3 ≤ h)", "theorem R_strictMono (h : ℕ) (hh : 2 ≤ h)"),
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
