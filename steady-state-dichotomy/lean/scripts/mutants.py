"""Mutation tests for the Lean files: each mutant plants one wrong count, sign, rate, Jacobian entry or root
interval and must make its file fail to compile. Run from lean/ after `lake build LeanProofs`."""
import subprocess, sys

MUTANTS = [
    ('LeanProofs/ZeroOneFour.lean', 'five positive states instead of four', 'S = {g r₁, g r₂, g r₃, g r₄} ∧ S.ncard = 4 ∧', 'S = {g r₁, g r₂, g r₃, g r₄} ∧ S.ncard = 5 ∧'),
    ('LeanProofs/ZeroOneFour.lean', 'first state det J positive (signs +,+,-,+)', '    detJ (X r₁) (Y r₁) r₁ < 0 ∧ 0 < detJ (X r₂) (Y r₂) r₂ ∧', '    0 < detJ (X r₁) (Y r₁) r₁ ∧ 0 < detJ (X r₂) (Y r₂) r₂ ∧'),
    ('LeanProofs/ZeroOneFour.lean', 'largest root in (94,95)', 'r₃ ∈ Ioo (6 / 5) (121 / 100) ∧ r₄ ∈ Ioo 93 94 ∧', 'r₃ ∈ Ioo (6 / 5) (121 / 100) ∧ r₄ ∈ Ioo 94 95 ∧'),
    ('LeanProofs/ZeroOneFour.lean', 'P coefficient 218 -> 217', 'def P (z : ℝ) : ℝ := z ^ 4 - 96 * z ^ 3 + 218 * z ^ 2 - 145 * z + 24', 'def P (z : ℝ) : ℝ := z ^ 4 - 96 * z ^ 3 + 217 * z ^ 2 - 145 * z + 24'),
    ('LeanProofs/ZeroOneFour.lean', 'inflow 0 -> X2 at rate 2', 'def f2 (x y z : ℝ) : ℝ := -8 * x * y + x * z + 1', 'def f2 (x y z : ℝ) : ℝ := -8 * x * y + x * z + 2'),
    ('LeanProofs/ZeroOneFour.lean', 'network bookkeeping: X1+X2 -> 0 at rate 6', '    f1 x y z = -7 * x * y - 1 * x * z + 1 * z + 1 * y * z - 1 * x * y ∧', '    f1 x y z = -6 * x * y - 1 * x * z + 1 * z + 1 * y * z - 1 * x * y ∧'),
    ('LeanProofs/ZeroOneFour.lean', 'Jacobian entry d f2/dz = -x', '     -8 * y + z, -8 * x, x;', '     -8 * y + z, -8 * x, -x;'),
    ('LeanProofs/ZeroOneFour.lean', 'det J coefficient -48 -> -47', 'def detJ (x y z : ℝ) : ℝ := -48 * x ^ 2', 'def detJ (x y z : ℝ) : ℝ := -47 * x ^ 2'),
    ('LeanProofs/ZeroOneFour.lean', 'curve x = (8z-1)/(z+23)', 'def X (z : ℝ) : ℝ := (8 * z - 1) / (z + 24)', 'def X (z : ℝ) : ℝ := (8 * z - 1) / (z + 23)'),
    ('LeanProofs/ZeroOneFour.lean', 'det J identity coefficient 191 -> 190', 'detJ (X z) (Y z) z = dP z / (z + 24) - (16 * z + 191) /', 'detJ (X z) (Y z) z = dP z / (z + 24) - (16 * z + 190) /'),
    ('LeanProofs/ZeroOneFive.lean', 'six positive states instead of five', 'S = {g r₁, g r₂, g r₃, g r₄, g r₅} ∧ S.ncard = 5 ∧', 'S = {g r₁, g r₂, g r₃, g r₄, g r₅} ∧ S.ncard = 6 ∧'),
    ('LeanProofs/ZeroOneFive.lean', 'four positive states instead of five', 'S = {g r₁, g r₂, g r₃, g r₄, g r₅} ∧ S.ncard = 5 ∧', 'S = {g r₁, g r₂, g r₃, g r₄, g r₅} ∧ S.ncard = 4 ∧'),
    ('LeanProofs/ZeroOneFive.lean', 'last state det J positive', '0 < detJ (X r₄) (Y r₄) r₄ ∧ detJ (X r₅) (Y r₅) r₅ < 0 := by', '0 < detJ (X r₄) (Y r₄) r₄ ∧ 0 < detJ (X r₅) (Y r₅) r₅ := by'),
    ('LeanProofs/ZeroOneFive.lean', 'smallest root interval shifted', 'r₁ ∈ Ioo (1 / 92549) (1 / 92548) ∧', 'r₁ ∈ Ioo (1 / 92548) (1 / 92547) ∧'),
    ('LeanProofs/ZeroOneFive.lean', 'rate X2 -> X1 doubled in f2', 'def f2 (x y z : ℝ) : ℝ := 1 / 2500 + x + x * z - 2 / 5 * y * z - 1 / 100000 * y', 'def f2 (x y z : ℝ) : ℝ := 1 / 2500 + x + x * z - 2 / 5 * y * z - 2 / 100000 * y'),
    ('LeanProofs/ZeroOneFive.lean', 'inflow 0 -> X1+X2 at 1/2000 in f1', 'def f1 (x y z : ℝ) : ℝ := 1 / 2500 - x', 'def f1 (x y z : ℝ) : ℝ := 1 / 2000 - x'),
    ('LeanProofs/ZeroOneFive.lean', 'network bookkeeping: X3 -> 0 at rate 1', '    f3 x y z = 5 * x - 2 / 5 * y * z - 1 / 2 * z := by', '    f3 x y z = 5 * x - 2 / 5 * y * z - 1 * z := by'),
    ('LeanProofs/ZeroOneFive.lean', 'eliminant coefficient 101000 -> 100000', '- 782738125 * z ^ 2 + 101000 * z - 1', '- 782738125 * z ^ 2 + 100000 * z - 1'),
    ('LeanProofs/ZeroOneFive.lean', 'Jacobian entry df3/dy = +2/5 z', '     5, -2 / 5 * z, -1 / 2 - 2 / 5 * y]', '     5, 2 / 5 * z, -1 / 2 - 2 / 5 * y]'),
    ('LeanProofs/ZeroOneFive.lean', 'M coefficient 8/5 -> 7/5', 'def M (z : ℝ) : ℝ := 8 / 5 * z', 'def M (z : ℝ) : ℝ := 7 / 5 * z'),
    ('LeanProofs/ZeroOneFive.lean', 'curve parametrisation D with 31999', 'def D (z : ℝ) : ℝ := 8000 * z ^ 2 - 32000 * z - 1', 'def D (z : ℝ) : ℝ := 8000 * z ^ 2 - 31999 * z - 1'),
]

killed = 0
for src, name, old, new in MUTANTS:
    text = open(src).read()
    assert text.count(old) == 1, f"{name}: anchor not unique in {src}"
    open(src, "w").write(text.replace(old, new))
    try:
        r = subprocess.run(["lake", "env", "lean", src], capture_output=True, text=True, timeout=900)
        dead = r.returncode != 0 or "error" in r.stdout + r.stderr
    finally:
        open(src, "w").write(text)
    killed += dead
    print(("killed   " if dead else "SURVIVED ") + f"{src}: {name}", flush=True)
print(f"{killed}/{len(MUTANTS)} mutants killed")
sys.exit(0 if killed == len(MUTANTS) else 1)
