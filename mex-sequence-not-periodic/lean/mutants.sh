#!/bin/zsh
# Mutation tests: each run plants one wrong change in a copy of the sources and checks that the copy
# no longer compiles. Every mutant must be rejected.
cd "${0:A:h}" || exit 1
run_mut() {
  name="$1"; file="$2"; expr="$3"
  rm -rf MexSequence/Mut; mkdir -p MexSequence/Mut
  for f in Basic Arith Main Twins; do
    sed -e 's/MexSequence\./MexSequence.Mut./g' MexSequence/$f.lean > MexSequence/Mut/$f.lean
  done
  cp MexSequence/Mut/$file.lean MexSequence/Mut/$file.orig
  sed -i '' "$expr" MexSequence/Mut/$file.lean
  if cmp -s MexSequence/Mut/$file.lean MexSequence/Mut/$file.orig; then echo "MUTATION DID NOT APPLY: $name"; return; fi
  target=MexSequence.Mut.Main; [[ $file == Twins ]] && target=MexSequence.Mut.Twins
  if nice -n 15 timeout 900 lake build $target >/dev/null 2>&1; then echo "MUTANT SURVIVED: $name"; else echo "rejected: $name"; fi
}
# the closed form (Appendix A)
run_mut "y slope 5"            Basic 's/+ 4 \* ((b - 3) \/ 3)/+ 5 * ((b - 3) \/ 3)/'
run_mut "w = 2 from block 2"   Basic 's/else if b ≤ 2 then 3 else 2/else if b ≤ 1 then 3 else 2/'
run_mut "start a 7 = 0"        Basic 's/a 6 = 1 ∧ a 7 = 1/a 6 = 1 ∧ a 7 = 0/'
run_mut "zeros at residues 0,2" Basic 's/n % 5 = 0 ∨ n % 5 = 3 then 0/n % 5 = 0 ∨ n % 5 = 2 then 0/'
run_mut "y cycle 2,4,5"        Basic 's/then 2 else if (b - 3) % 3 = 1 then 5 else 4/then 2 else if (b - 3) % 3 = 1 then 4 else 5/'
# the route of Section 4 (Lemmas 1 and 2)
run_mut "Lemma 1: zeros at residues 0,2" Twins 's/m ≠ 0 ∧ (m % 5 = 0 ∨ m % 5 = 3)/m ≠ 0 ∧ (m % 5 = 0 ∨ m % 5 = 2)/'
run_mut "Lemma 1: a 0 also zero"         Twins 's/a m = 0 ↔ m ≠ 0 ∧/a m = 0 ↔ True ∧/'
run_mut "Lemma 2: twins at 5b+1, 5b+3"   Twins 's/∀ b, a (5 \* b + 1) = a (5 \* b + 2) ∧/∀ b, a (5 * b + 1) = a (5 * b + 3) ∧/'
run_mut "Lemma 2: new from block 1"      Twins 's/(2 ≤ b → ∀ c < b, a (5 \* b + 1) ≠ a (5 \* c + 1))/(1 ≤ b → ∀ c < b, a (5 * b + 1) ≠ a (5 * c + 1))/'
run_mut "Lemma 2: differs from 4th col"  Twins 's/(2 ≤ b → ∀ c < b, a (5 \* b + 1) ≠ a (5 \* c + 1))/(2 ≤ b → ∀ c < b, a (5 * b + 1) ≠ a (5 * c + 4))/'
rm -rf MexSequence/Mut .lake/build/lib/lean/MexSequence/Mut .lake/build/ir/MexSequence/Mut
