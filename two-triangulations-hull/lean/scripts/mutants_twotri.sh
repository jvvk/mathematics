#!/bin/bash
# Mutation tests for LeanProofs/TwoTri: each mutant must FAIL to compile.
cd "$(dirname "$0")/.." || exit 1
S="${TMPDIR:-/tmp}/twotri_mut"; mkdir -p "$S"
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
mutate LeanProofs/TwoTri/Main.lean "f n = 5 := by" "f n = 4 := by" "Theorem 1 with f(n) = 4"
mutate LeanProofs/TwoTri/Upper.lean "theorem upper_rat (n : ℕ) (hn : 9 ≤ n)" "theorem upper_rat (n : ℕ) (hn : 8 ≤ n)" "induction from n = 8"
mutate LeanProofs/TwoTri/Cor.lean "5 ≤ (A ∩ B).card ∧ ((A ∩ B).card = 5" "6 ≤ (A ∩ B).card ∧ ((A ∩ B).card = 5" "lower bound 6"
mutate LeanProofs/TwoTri/Nine.lean "def p5 : ℚ × ℚ := (28, 26)" "def p5 : ℚ × ℚ := (28, 30)" "point 5 moved"
mutate LeanProofs/TwoTri/Nine.lean "s(p7, p8)}" "s(p6, p8)}" "triangulation A loses edge 78"
mutate LeanProofs/TwoTri/Nine.lean "⟨1 / 2, by norm_num, by norm_num" "⟨1 / 10, by norm_num, by norm_num" "invariant witness off the face"
mutate LeanProofs/TwoTri/Lower.lean "(hside : ∀ r ∈ P, r ≠ u → ℓ u < ℓ r)" "(hside : ∀ r ∈ P, r ≠ u → ℓ u ≤ ℓ r)" "sweep with a weak side condition"
mutate LeanProofs/TwoTri/Insert.lean "(hg : Generic P p) : IsTri (insert p P)" "(hg : True) : IsTri (insert p P)" "insertion without genericity"
mutate LeanProofs/TwoTri/EdgeCount.lean "T.card + 3 + (hullEdges P).card = 3 * P.card := by
  classical
  obtain" "T.card + 4 + (hullEdges P).card = 3 * P.card := by
  classical
  obtain" "edge count 3n-4-h"
mutate LeanProofs/TwoTri/Oct.lean "(minShared P : ℤ) = 6 * P.card - 6 -" "(minShared P : ℤ) = 6 * P.card - 5 -" "oct formula off by one"
mutate LeanProofs/TwoTri/Oct.lean "theorem pentagon : minShared P5 = 5 ∧ oct P5 = 1" "theorem pentagon : minShared P5 = 5 ∧ oct P5 = 2" "pentagon oct = 2"
mutate LeanProofs/TwoTri/Regen5d.lean "theorem regeneration {P : Finset (K × K)} (hP : GenPos P) (h7 : 7 ≤ P.card)" "theorem regeneration {P : Finset (K × K)} (hP : GenPos P) (h7 : 6 ≤ P.card)" "regeneration for six points"
mutate LeanProofs/TwoTri/Fan.lean "∃ w ∈ P, s(v, w) ∈ T ∧ dotd d v w < 0 := by
  classical" "∃ w ∈ P, s(v, w) ∈ T ∧ dotd d v w < -1 := by
  classical" "fan lemma with a margin"
mutate LeanProofs/TwoTri/Extend.lean "(hcard : S.card + 3 + (hullEdges P).card = 3 * P.card) : IsTri P S" "(hcard : S.card + 2 + (hullEdges P).card = 3 * P.card) : IsTri P S" "edge criterion with one edge fewer"
echo "$pass/$total mutants killed"
