"""Mutation harness for LeanProofs/MaxPaths: every mutant must be rejected by Lean."""
import os, subprocess, sys, tempfile

D = "LeanProofs/MaxPaths/"
MUTANTS = [
    ("Main.lean", "fam61 intercept", "IsMax 5 E61 0 3 a (6 * a + 1)", "IsMax 5 E61 0 3 a (6 * a + 3)"),
    ("Main.lean", "fam69 slope", "IsMax 6 E69 2 4 a (6 * a + 9)", "IsMax 6 E69 2 4 a (5 * a + 9)"),
    ("Main.lean", "W4 value", "IsMax 5 EW4 0 0 0 9", "IsMax 5 EW4 0 0 0 8"),
    ("Main.lean", "E61 edge dropped", "(1, 4), (2, 3), (2, 4)]", "(1, 4), (2, 3)]"),
    ("Main.lean", "k = 3 allowed", "(h3 : k ≠ 3)", "(h3 : True)"),
    ("Main.lean", "fam611 wrong witness", "witness0 (by norm_num) (by norm_num) 1 4", "witness0 (by norm_num) (by norm_num) 1 3"),
    ("Family.lean", "affine coefficient", "= N h E x y b s t + (a - b) * T h E x y b s t := by\n  set P", "= N h E x y b s t + (a - b + 1) * T h E x y b s t := by\n  set P"),
    ("Paths.lean", "at most one without head condition", "(m₁ : n₁ ∈ l) (m₂ : n₂ ∈ l) (e₁ : l.head? ≠ some n₁) (e₁' : l.getLast? ≠ some n₁)", "(m₁ : n₁ ∈ l) (m₂ : n₂ ∈ l) (e₁' : l.getLast? ≠ some n₁)"),
    ("Paths.lean", "pullback without injectivity", "(E : W → V)\n    (hE : Function.Injective E) (hadj", "(E : W → V)\n    (hadj"),
    ("Paths.lean", "generator fuel off by one", "∃ q, l = q ++ p ∧ q.length ≤ n ∧ l.Nodup ∧ l.IsChain (R adj)\n  | 0", "∃ q, l = q ++ p ∧ q.length ≤ n + 1 ∧ l.Nodup ∧ l.IsChain (R adj)\n  | 0"),
]

tmpdir = tempfile.mkdtemp(dir=os.environ.get("TMPDIR"))
killed = 0
for fname, name, old, new in MUTANTS:
    src = open(D + fname).read()
    assert src.count(old) == 1, f"pattern not unique: {name}"
    path = os.path.join(tmpdir, "Mutant.lean")
    open(path, "w").write(src.replace(old, new))
    r = subprocess.run(["lake", "env", "lean", path], capture_output=True, text=True, timeout=1200)
    ok = r.returncode != 0 or "error" in r.stdout
    killed += ok
    print(("killed  " if ok else "SURVIVED"), name, flush=True)
os.remove(os.path.join(tmpdir, "Mutant.lean")); os.rmdir(tmpdir)
print(f"{killed}/{len(MUTANTS)} mutants killed")
sys.exit(0 if killed == len(MUTANTS) else 1)
