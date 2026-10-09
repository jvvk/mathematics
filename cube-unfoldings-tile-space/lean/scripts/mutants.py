#!/usr/bin/env python3
"""Mutation tests for LeanProofs/CubeUnfoldings (unfoldings of the cube tile space): every wrong
variant must FAIL to check.

Each mutant copies one file to CubeUnfoldings/Mut.lean with a single textual change and compiles it
with `lake env lean` (single process, background QoS). Unmutated copies must pass (baseline).
"""
import os
import pathlib
import signal
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
D = ROOT / "LeanProofs" / "CubeUnfoldings"
MUT = D / "Mut.lean"

MUTANTS = [
    ("tiling: exactly once -> at least once", "Quotients.lean",
     "  ∀ x : V, ∃! q : β × L, q.1 ∈ S ∧ x = c q.1 + q.2", "  ∀ x : V, ∃ q : β × L, q.1 ∈ S ∧ x = c q.1 + q.2"),
    ("Lemma 4 without disjoint images", "Quotients.lean",
     "      Set.InjOn φ P ∧ Set.InjOn φ Q ∧ Disjoint (P.image φ) (Q.image φ) := by",
     "      Set.InjOn φ P ∧ Set.InjOn φ Q := by"),
    ("Lemma 5 with group order |P|", "Quotients.lean",
     "(hG : Fintype.card G = 2 * P.card) (hP : Set.InjOn φ P)\n    (t : V)",
     "(hG : Fintype.card G = P.card) (hP : Set.InjOn φ P)\n    (t : V)"),
    ("second tile translated, not reflected", "Quotients.lean",
     "P.image (fun p => t - p)", "P.image (fun p => t + p)"),
    ("phi coefficient 4 -> 3", "Example.lean",
     "4 * (x 0 : ZMod 10)", "3 * (x 0 : ZMod 10)"),
    ("t moved", "Example.lean", "def t5 : Fin 4 → ℤ := ![-1, -1, 0, -1]", "def t5 : Fin 4 → ℤ := ![-1, -1, 0, 0]"),
    ("one cell moved", "Example.lean", "![1, 0, 0, -1], ![2, 0, 0, 0]}", "![1, 0, 0, -1], ![2, 0, 1, 0]}"),
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
