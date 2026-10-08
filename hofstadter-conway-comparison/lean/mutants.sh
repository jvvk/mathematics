#!/bin/zsh
# Mutation tests for HofstadterConway: each run copies the sources to HofstadterConway/Mut, plants one
# wrong change, and builds the copy through Corollary.lean (which imports everything). Every mutant must
# FAIL to build; the unchanged copy (control) must build. Run from this folder after `lake build`.
cd "${0:A:h}" || exit 1
ok=1
FILES=(Basic Ops Tee Key Blocks Main Corollary)
copy() {
  rm -rf HofstadterConway/Mut; mkdir -p HofstadterConway/Mut
  for f in $FILES; do
    sed -e 's/HofstadterConway\./HofstadterConway.Mut./g' HofstadterConway/$f.lean > HofstadterConway/Mut/$f.lean
  done
}
build() { nice -n 15 timeout 2400 lake build HofstadterConway.Mut.Corollary >/dev/null 2>&1 }
copy
if build; then echo "control builds"; else echo "CONTROL FAILED"; ok=0; fi
run_mut() {
  name="$1"; file="$2"; expr="$3"
  copy
  cp HofstadterConway/Mut/$file.lean HofstadterConway/Mut/$file.orig
  sed -i '' "$expr" HofstadterConway/Mut/$file.lean
  if cmp -s HofstadterConway/Mut/$file.lean HofstadterConway/Mut/$file.orig; then echo "NOT APPLIED: $name"; ok=0; return; fi
  rm HofstadterConway/Mut/$file.orig
  if build; then echo "MUTANT SURVIVED: $name"; ok=0; else echo "rejected: $name"; fi
}
run_mut "c reads c(n-1-x)"              Basic 's/then c x + c (n + 3 - x) else 0/then c x + c (n + 2 - x) else 0/'
run_mut "s reads s(n-1-x)"              Basic 's/then n + 3 - s x - s (n + 3 - x) else 0/then n + 3 - s x - s (n + 2 - x) else 0/'
run_mut "s(2) = 2"                      Basic '/^def s :/,/termination_by/s/  | 2 => 1/  | 2 => 2/'
run_mut "recurrence (2.4) shifted"      Ops   's/  | j + 1 => P (Arec P j) + P (j + 1 - Arec P j)/  | j + 1 => P (Arec P j) + P (j - Arec P j)/'
run_mut "recurrence (2.5) unshifted"    Ops   's/  | j + 1 => P (Brec P j + 1) + P (j - Brec P j)/  | j + 1 => P (Brec P j) + P (j - Brec P j)/'
run_mut "T without the lowering"        Tee   's/if i < L \/ 2 then P (i + 1) - 1 else/if i < L \/ 2 then P (i + 1) else/'
run_mut "T without the central swap"    Tee   's/else if i = L \/ 2 then P (L \/ 2 - 1) else/else if i = L \/ 2 then P (L \/ 2) else/'
run_mut "key lemma with a gap of 1"     Key   's/    GP (2 \* L) (FP L (TP L P)) i ≤ TP (2 \* (2 \* L)) (FP (2 \* L) (FP L P)) i := by/    GP (2 * L) (FP L (TP L P)) i + 1 ≤ TP (2 * (2 * L)) (FP (2 * L) (FP L P)) i := by/'
run_mut "odd blocks strictly below T"   Main  's/theorem odd_blocks (n : ℕ) : ∀ i, vP (2 \* n + 3) i ≤ TP/theorem odd_blocks (n : ℕ) : ∀ i, vP (2 * n + 3) i < TP/'
run_mut "Theorem 1: s < c"              Main  's/theorem main (n : ℕ) (hn : 1 ≤ n) : n ≤ c n + s n ∧ s n ≤ c n := by/theorem main (n : ℕ) (hn : 1 ≤ n) : n ≤ c n + s n ∧ s n < c n := by/'
run_mut "Theorem 1: strict"             Main  's/    |(s n : ℚ) - n \/ 2| ≤ c n - n \/ 2 := by/    |(s n : ℚ) - n \/ 2| < c n - n \/ 2 := by/'
run_mut "Lemma 2.1: letters sum to 2"   Corollary 's/letter P (L + 1 - i) + letter P i = 1 := by/letter P (L + 1 - i) + letter P i = 2 := by/'
run_mut "Corollary 4.2: s(2^k) = 2^k"   Corollary 's/c (2 \^ k) = 2 \^ (k - 1) ∧ s (2 \^ k) = 2 \^ (k - 1) := by/c (2 ^ k) = 2 ^ (k - 1) ∧ s (2 ^ k) = 2 ^ k := by/'
run_mut "Corollary 4.2: sign parity swapped" Corollary 's/(k % 2 = 0 → n ≤ 2 \* s n) ∧ (k % 2 = 1 → 2 \* s n ≤ n)/(k % 2 = 1 → n ≤ 2 * s n) ∧ (k % 2 = 0 → 2 * s n ≤ n)/'
run_mut "Corollary 4.2: s jumps by 2"   Corollary 's/s n ≤ s (n + 1) ∧ s (n + 1) ≤ s n + 1 := by/s n + 1 ≤ s (n + 1) ∧ s (n + 1) ≤ s n + 1 := by/'
run_mut "Lemma 4.3: v_(k+1) in place of v_k" Blocks 's/theorem v_symm : ∀ k, 1 ≤ k → Symm (2 ^ k) (vP k) := by/theorem v_symm : ∀ k, 1 ≤ k → Symm (2 ^ k) (vP (k + 1)) := by/'
rm -rf HofstadterConway/Mut .lake/build/lib/lean/HofstadterConway/Mut .lake/build/ir/HofstadterConway/Mut
if [[ $ok == 1 ]]; then echo "ALL MUTANTS REJECTED, CONTROL BUILDS"; else echo "FAILURES ABOVE"; exit 1; fi
