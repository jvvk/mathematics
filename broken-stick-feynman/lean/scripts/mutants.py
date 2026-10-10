#!/usr/bin/env python3
"""Mutation tests for LeanProofs/BrokenStick.lean ("A broken stick and a Feynman diagram", MO 142983):
every wrong variant must FAIL to check.

Each mutant copies the file to LeanProofs/BrokenStickMut.lean with a single textual change and compiles it
with `lake env lean` (single process, nice 15). The unmutated copy must pass (baseline).
"""
import pathlib
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
SRC = ROOT / "LeanProofs" / "BrokenStick.lean"
MUT = ROOT / "LeanProofs" / "BrokenStickMut.lean"

MUTANTS = [
    ("Kirchhoff polynomial keeps the triangle 123", "  - (t01*t02*t12 + t01*t03*t13 + t02*t03*t23 + t12*t13*t23)",
     "  - (t01*t02*t12 + t01*t03*t13 + t02*t03*t23)"),
    ("Symanzik polynomial removes a wrong star", "  - (b03*b13*b23 + b02*b12*b23 + b01*b12*b13 + b01*b02*b03)",
     "  - (b03*b13*b12 + b02*b12*b23 + b01*b12*b13 + b01*b02*b03)"),
    ("Gram map determinant -4", "theorem det_gramMap3 : gramMap3.det = -8 := by", "theorem det_gramMap3 : gramMap3.det = -4 := by"),
    ("triangle Gram map determinant -1", "Matrix (Fin 3) (Fin 3) ℝ).det = -2 := by", "Matrix (Fin 3) (Fin 3) ℝ).det = -1 := by"),
    ("20 spanning trees", "s ∉ triangles)).card = 16 := by", "s ∉ triangles)).card = 20 := by"),
    ("C3 = 3/pi", "theorem C3_eq : C3 = 4 / π := by", "theorem C3_eq : C3 = 3 / π := by"),
    ("C2 = 2/sqrt pi", "theorem C2_eq : C2 = 1 / sqrt π := by", "theorem C2_eq : C2 = 2 / sqrt π := by"),
    ("triangle probability 1/3", "theorem p2_eq_quarter : C2 * Gamma (3 / 2) / 2 = 1 / 4 := by",
     "theorem p2_eq_quarter : C2 * Gamma (3 / 2) / 2 = 1 / 3 := by"),
    ("Feynman normalisation pi^2/8", "theorem C3_feynman : C3 * Gamma (3 / 2) ^ 6 = π ^ 2 / 16 := by",
     "theorem C3_feynman : C3 * Gamma (3 / 2) ^ 6 = π ^ 2 / 8 := by"),
    ("homogeneity degree -N/3", "    N * ((n - 2) / 2) - (N - n) * ((n + 1) / 2) = -N / 2 := by",
     "    N * ((n - 2) / 2) - (N - n) * ((n + 1) / 2) = -N / 3 := by"),
    ("trace identity with g12 for 2 g12", "        + t23 * (g22 + g33 - 2 * g23)\n",
     "        + t23 * (g22 + g33 - g23)\n"),
    ("substitution with 4^2", "      = symanzik3 b01 b02 b03 b12 b13 b23 / (4 ^ 3 * (b01 * b02 * b03 * b12 * b13 * b23)) := by",
     "      = symanzik3 b01 b02 b03 b12 b13 b23 / (4 ^ 2 * (b01 * b02 * b03 * b12 * b13 * b23)) := by"),
    ("Schwinger Jacobian without the 1/2", "    2 * sqrt β * (1 / (4 * β ^ 2)) = 1 / (2 * (β * sqrt β)) := by",
     "    2 * sqrt β * (1 / (4 * β ^ 2)) = 1 / (β * sqrt β) := by"),
    ("N - n(n-1)/2 = n + 1", "theorem edges_minus_offdiag (n : ℕ) : n * (n + 1) / 2 - n * (n - 1) / 2 = n := by",
     "theorem edges_minus_offdiag (n : ℕ) : n * (n + 1) / 2 - n * (n - 1) / 2 = n + 1 := by"),
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
