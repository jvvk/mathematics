#!/usr/bin/env python3
"""Mutation tests for LeanProofs/TanhResidues.lean (residues of prod (1-q^k)/(1+q^k), MSE 5150767):
every wrong variant must FAIL to check.

Each mutant copies the file to LeanProofs/TanhResiduesMut.lean with a single textual change and compiles it
with `lake env lean` (single process, nice 15). The unmutated copy must pass (baseline).
"""
import pathlib
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
SRC = ROOT / "LeanProofs" / "TanhResidues.lean"
MUT = ROOT / "LeanProofs" / "TanhResiduesMut.lean"

MUTANTS = [
    ("constant with 2^e", "      2 / m * 4 ^ e * (e.factorial : ℚ) ^ 2 / (2 * e + 1).factorial := by",
     "      2 / m * 2 ^ e * (e.factorial : ℚ) ^ 2 / (2 * e + 1).factorial := by"),
    ("factor +i tan", "      -Complex.I * (Real.tan (θ / 2) : ℂ) := by", "      Complex.I * (Real.tan (θ / 2) : ℂ) := by"),
    ("pairing without inverse", "    Real.tan (ang m j (m - k)) = (Real.tan (ang m j k))⁻¹ := by",
     "    Real.tan (ang m j (m - k)) = Real.tan (ang m j k) := by"),
    ("reflection keeps sign", "    Real.tan (ang m j (2 * m - k)) = -Real.tan (ang m j k) := by",
     "    Real.tan (ang m j (2 * m - k)) = Real.tan (ang m j k) := by"),
    ("tail without minus", "    Real.tan (ang m j (m + k)) = -(Real.tan (ang m j k))⁻¹ := by",
     "    Real.tan (ang m j (m + k)) = (Real.tan (ang m j k))⁻¹ := by"),
    ("tan nonzero up to k = m", "theorem tan_ne_zero (m j : ℕ) (hj : Nat.Coprime j m) (k : ℕ) (hk0 : 0 < k) (hkm : k < m) :",
     "theorem tan_ne_zero (m j : ℕ) (hj : Nat.Coprime j m) (k : ℕ) (hk0 : 0 < k) (hkm : k ≤ m) :"),
    ("eps = -1 for odd m", "noncomputable def eps (m j : ℕ) : ℝ := if Even m then Real.tan (π * j / 4) else 1",
     "noncomputable def eps (m j : ℕ) : ℝ := if Even m then Real.tan (π * j / 4) else -1"),
    ("symmetry m - rho", "    A m j ρ = eps m j * A m j (m - 1 - ρ) := by", "    A m j ρ = eps m j * A m j (m - ρ) := by"),
    ("residue power (-i)^m", "      (-Complex.I) ^ (m - 1) * (eps m j : ℂ) *", "      (-Complex.I) ^ m * (eps m j : ℂ) *"),
    ("inversion sign (-1)^(n+1)",
     "    ∏ k ∈ Icc 1 n, (1 - q⁻¹ ^ k) / (1 + q⁻¹ ^ k) = (-1) ^ n * ∏ k ∈ Icc 1 n, (1 - q ^ k) / (1 + q ^ k) := by",
     "    ∏ k ∈ Icc 1 n, (1 - q⁻¹ ^ k) / (1 + q⁻¹ ^ k) = (-1) ^ (n + 1) * ∏ k ∈ Icc 1 n, (1 - q ^ k) / (1 + q ^ k) := by"),
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
