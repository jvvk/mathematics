"""Mutation harness for LeanProofs/DeBruijnCycles/Basic.lean: every mutant statement must be rejected."""
import os, subprocess, sys, tempfile

SRC = "LeanProofs/DeBruijnCycles/Basic.lean"
MUTANTS = [
    ("ratio sign", "= (2 ^ n + (-1) ^ (n + 1)) / (3 * 2 ^ n) := by\n  rw [geom_sum_eq", "= (2 ^ n - (-1) ^ (n + 1)) / (3 * 2 ^ n) := by\n  rw [geom_sum_eq"),
    ("quadratic form", "= 2 * (-1 / 2) ^ k := by", "= 2 * (1 / 2) ^ k := by"),
    ("mixing time", "(P m ^ m) u v = (1 / 2) ^ m := by", "(P m ^ m) u v = (1 / 2) ^ (m + 1) := by"),
    ("parity of returns", "cnt m k (pv m) (pv m) = if k % 2 = 0 then 1 else 0", "cnt m k (pv m) (pv m) = if k % 2 = 0 then 0 else 1"),
    ("case B factor", "(lap (n + 1) (2 • P (n + 1)) + J (n + 1)).det * ((2 ^ n + (-1) ^ (n + 1)) / (3 * 2 ^ n))", "(lap (n + 1) (2 • P (n + 1)) + J (n + 1)).det * ((2 ^ n + (-1) ^ (n + 1)) / (3 * 2 ^ (n + 1)))"),
    ("total sign", "* (2 ^ (n + 2) - (-1) ^ (n + 2)) / 3", "* (2 ^ (n + 2) + (-1) ^ (n + 2)) / 3"),
    ("classification", "∨ ((u₁, b₁) = (pv m, false) ∧ (u₂, b₂) = (qv m, true))", "∨ ((u₁, b₁) = (pv m, false) ∧ (u₂, b₂) = (qv m, false))"),
    ("closed form third", "= 1 / 3 * 2 ^ (2 ^ (n + 1) - 2 * (n + 1)) * (2 ^ n + (-1) ^ (n + 1)) := by\n  rw [exp_split, pow_add]\n  field_simp", "= 1 / 2 * 2 ^ (2 ^ (n + 1) - 2 * (n + 1)) * (2 ^ n + (-1) ^ (n + 1)) := by\n  rw [exp_split, pow_add]\n  field_simp"),
    ("rank-one sign", "= lap m A - vecMulVec (w m) (w m) := by", "= lap m A + vecMulVec (w m) (w m) := by"),
]

src = open(SRC).read()
tmpdir = tempfile.mkdtemp(dir=os.environ.get("TMPDIR"))
killed = 0
for name, old, new in MUTANTS:
    assert src.count(old) == 1, f"pattern not unique: {name}"
    path = os.path.join(tmpdir, "Mutant.lean")
    open(path, "w").write(src.replace(old, new))
    r = subprocess.run(["lake", "env", "lean", path], capture_output=True, text=True, timeout=900)
    ok = r.returncode != 0 or "error" in r.stdout
    killed += ok
    print(("killed  " if ok else "SURVIVED"), name, flush=True)
os.remove(os.path.join(tmpdir, "Mutant.lean")); os.rmdir(tmpdir)
print(f"{killed}/{len(MUTANTS)} mutants killed")
sys.exit(0 if killed == len(MUTANTS) else 1)
