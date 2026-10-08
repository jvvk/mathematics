#!/bin/bash
# Mutation tests for LeanProofs/TwoTri/Hulls.lean (Theorem 2): each mutant must FAIL to compile.
cd "$(dirname "$0")/.." || exit 1
S="${TMPDIR:-/tmp}/hulls_mut"; mkdir -p "$S"
pass=0; total=0
mutate() {  # file  old  new  label
  local f="$1" old="$2" new="$3" label="$4"
  total=$((total+1))
  cp "$f" "$S/orig.lean"
  OLD="$old" NEW="$new" F="$f" ~/.venvs/main/bin/python - <<'PY'
import os
from pathlib import Path
p = Path(os.environ["F"]); s = p.read_text()
assert os.environ["OLD"] in s, "mutation target not found"
p.write_text(s.replace(os.environ["OLD"], os.environ["NEW"], 1))
PY
  if nice -n 15 timeout 300 lake env lean --threads=1 "$f" 2>&1 | grep -q "error"; then
    echo "KILLED   $label"; pass=$((pass+1))
  else
    echo "SURVIVED $label"
  fi
  cp "$S/orig.lean" "$f"
}
F=LeanProofs/TwoTri/Hulls.lean
mutate $F "HullOnly n h ↔ n = h ∨ 6 ≤ h ∨" "HullOnly n h ↔ n = h ∨ 5 ≤ h ∨" "Theorem 2 with h >= 5"
mutate $F "HullOnly n h ↔ n = h ∨ 6 ≤ h ∨ (h = 5 ∧ 9 ≤ n)" "HullOnly n h ↔ n = h ∨ 6 ≤ h ∨ (h = 5 ∧ 8 ≤ n)" "pentagon from n = 8"
mutate $F "theorem not_hullOnly_small {n h : ℕ} (h3 : 3 ≤ h) (h4 : h ≤ 4)" "theorem not_hullOnly_small {n h : ℕ} (h3 : 3 ≤ h) (h4 : h ≤ 5)" "small-hull bound for a pentagon"
mutate $F "HullR h i j ∨ (i = 0 ∧ j = 2) ∨ (i = 2 ∧ j = 4) ∨ (i = 0 ∧ j = 4) ∨ (i = 4 ∧ 6 ≤ j)" "HullR h i j ∨ (i = 0 ∧ j = 2) ∨ (i = 2 ∧ j = 4) ∨ (i = 0 ∧ j = 4) ∨ (i = 4 ∧ 7 ≤ j)" "seed A loses the edge v5v7"
mutate $F "HullR h i j ∨ (i = 1 ∧ j = 3) ∨ (i = 3 ∧ j = 5) ∨ (i = 1 ∧ j = 5) ∨ (i = 1 ∧ 6 ≤ j)" "HullR h i j ∨ (i = 1 ∧ j = 3) ∨ (i = 3 ∧ j = 5) ∨ (i = 1 ∧ j = 5) ∨ (i = 4 ∧ 6 ≤ j)" "seed B fans from v5 (shares edges with A)"
mutate $F "def HullR (h i j : ℕ) : Prop := j = i + 1 ∨ (i = 0 ∧ j = h - 1)" "def HullR (h i j : ℕ) : Prop := j = i + 1 ∨ (i = 0 ∧ j = h - 2)" "wrong closing hull edge"
mutate $F "def q7 : ℚ × ℚ := (2, 1)" "def q7 : ℚ × ℚ := (3, 1)" "seven points: point 7 moved"
mutate $F "⟨13 / 20, by norm_num, by norm_num, by norm_num [InTri, orient, lerp, par]⟩" "⟨1 / 20, by norm_num, by norm_num, by norm_num [InTri, orient, lerp, par]⟩" "seed invariant witness off the face"
mutate $F "def Inter (i j k l : ℕ) : Prop := (i < k ∧ k < j ∧ j < l) ∨ (k < i ∧ i < l ∧ l < j)" "def Inter (i j k l : ℕ) : Prop := (i < k ∧ k < j ∧ j < l)" "one-sided interleaving"
echo "$pass/$total mutants killed"
