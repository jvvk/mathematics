#!/usr/bin/env python3
"""Mutation tests for LeanProofs/QNarayana ("Even and odd Dyck paths", MO 501839): every wrong variant must FAIL to check.

Each mutant copies one file to QNarayana/Mut.lean with a single textual change and compiles it with
`lake env lean` (single process, nice 15). Unmutated copies must pass (baseline).
"""
import pathlib
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
D = ROOT / "LeanProofs" / "QNarayana"
MUT = D / "Mut.lean"

MUTANTS = [
    ("partner of ud is ab, not ba", "Words.lean", "  | u, d => some (b, a)", "  | u, d => some (a, b)"),
    ("du <-> ab allowed at height 0", "Words.lean",
     "  | d, u => if 1 ≤ h then some (a, b) else none", "  | d, u => if 0 ≤ h then some (a, b) else none"),
    ("ab treated as unpartnered at every height", "Words.lean", "  | a, b => h == 0", "  | a, b => decide (0 ≤ h)"),
    ("sign of fixed points claimed (-1)^(t+1)", "Words.lean",
     "h = 2 * t → F h w = true → sgnFrom p w = (-1) ^ t", "h = 2 * t → F h w = true → sgnFrom p w = (-1) ^ (t + 1)"),
    ("last departure test inverted", "Bijection.lean",
     "  | u => if minRel p = 0 then (a, b) else (u, u)", "  | u => if minRel p = 0 then (u, u) else (a, b)"),
    ("halving sends ab to a level letter", "Bijection.lean", "  | a, b => u\n", "  | a, b => b\n"),
    ("decoder: up phase ignores the flag", "Dyck.lean",
     "  | true, f :: p, v => true :: dec (!f) p v", "  | true, f :: p, v => true :: dec f p v"),
    ("valley position off by one", "Dyck.lean",
     "  | i, pd, s :: P => (if pd && s then i else 0) + majP (i + 1) (!s) P",
     "  | i, pd, s :: P => (if pd && s then i + 1 else 0) + majP (i + 1) (!s) P"),
    ("letters u and d exchanged", "Dyck.lean", "  | false, true => u\n  | true, false => d",
     "  | false, true => d\n  | true, false => u"),
    ("symmetry = plain reversal", "Dyck.lean",
     "∑ P ∈ Dyck n k, (-1 : ℤ) ^ maj P = ((Dyck n k).filter (fun P => rc P = P)).card := by",
     "∑ P ∈ Dyck n k, (-1 : ℤ) ^ maj P = ((Dyck n k).filter (fun P => P.reverse = P)).card := by"),
    ("weight k instead of 2k", "Dyck.lean",
     "    decW w ∈ Dyck n k ∧ encW (decW w) = w := by", "    decW w ∈ Dyck n (2 * k) ∧ encW (decW w) = w := by"),
    ("Dyck condition ends at height 1", "Dyck.lean", "  | h, [] => h == 0\n  | h, s :: P => decide",
     "  | h, [] => h == 1\n  | h, s :: P => decide"),
]


def check(text: str) -> bool:
    MUT.write_text(text)
    r = subprocess.run(["nice", "-n", "15", "lake", "env", "lean", str(MUT)], cwd=ROOT,
                       capture_output=True, text=True, timeout=900)
    return r.returncode == 0 and "error" not in r.stdout


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
