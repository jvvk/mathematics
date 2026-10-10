#!/usr/bin/env python3
"""Mutation tests for LeanProofs/AcuteRadial.lean ("Acute triangles on concentric spheres", MO 484567):
every wrong variant must FAIL to check.

Each mutant copies the file to LeanProofs/AcuteRadialMut.lean with a single textual change and compiles it
with `lake env lean` (single process, nice 15). The unmutated copy must pass (baseline).
"""
import pathlib
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
SRC = ROOT / "LeanProofs" / "AcuteRadial.lean"
MUT = ROOT / "LeanProofs" / "AcuteRadialMut.lean"

MUTANTS = [
    ("obtuse at c: c^2/(6ab)", "obtuse a b c = 1 / 2 - c ^ 2 / (3 * a * b) := by", "obtuse a b c = 1 / 2 - c ^ 2 / (6 * a * b) := by"),
    ("obtuse at b: c^2/(3ab)", "obtuse a c b = (a - b) / (2 * a) + c ^ 2 / (6 * a * b) := by", "obtuse a c b = (a - b) / (2 * a) + c ^ 2 / (3 * a * b) := by"),
    ("obtuse at a: h^3/(3abc)", "^ 2)) ^ 3 / (6 * a * b * c) := by", "^ 2)) ^ 3 / (3 * a * b * c) := by"),
    ("integrand with 4uvw", "((K - (M - w) ^ 2) / (8 * u * v * w))", "((K - (M - w) ^ 2) / (4 * u * v * w))"),
    ("bound 1/3", "theorem acute_le_half (hab : b ≤ a) (hbc : c ≤ b) (hc : 0 < c) : acute a b c ≤ 1 / 2 := by",
     "theorem acute_le_half (hab : b ≤ a) (hbc : c ≤ b) (hc : 0 < c) : acute a b c ≤ 1 / 3 := by"),
    ("strict bound with a = b allowed", "theorem acute_lt_half (hab : b < a)", "theorem acute_lt_half (hab : b ≤ a)"),
    ("space mixture 1 + 3e", "(1 - ε) ^ 2 * (1 + 2 * ε) / 2 ∧", "(1 - ε) ^ 2 * (1 + 3 * ε) / 2 ∧"),
    ("plane slope 1/2", "(fun ε : ℝ => (1 - ε) ^ 2 * (1 + 5 * ε) / 4) (3 / 4) 0", "(fun ε : ℝ => (1 - ε) ^ 2 * (1 + 5 * ε) / 4) (1 / 2) 0"),
    ("obtuse condition with <=", "    inner ℝ (U - W) (V - W) < 0 ↔", "    inner ℝ (U - W) (V - W) ≤ 0 ↔"),
    ("uniform tail over L", "= max 0 (min 1 ((L - T) / (2 * L))) := by", "= max 0 (min 1 ((L - T) / L)) := by"),
]


def check(text: str) -> bool:
    MUT.write_text(text)
    r = subprocess.run(["nice", "-n", "15", "lake", "env", "lean", str(MUT)], cwd=ROOT,
                       capture_output=True, text=True, timeout=900)
    return r.returncode == 0 and "error" not in r.stdout


def main() -> int:
    src = SRC.read_text()
    bad = 0
    try:
        if not check(src):
            print("BASELINE FAILS")
            return 1
        print("baseline: passes")
        for name, old, new in MUTANTS:
            if src.count(old) != 1:
                print(f"SETUP ERROR ({src.count(old)} matches): {name}")
                bad += 1
                continue
            ok = check(src.replace(old, new))
            print(f"{'SURVIVED' if ok else 'rejected'}: {name}")
            bad += ok
    finally:
        MUT.unlink(missing_ok=True)
    print(f"{len(MUTANTS) - bad}/{len(MUTANTS)} mutants rejected")
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
