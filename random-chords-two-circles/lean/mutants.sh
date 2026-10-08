#!/bin/zsh
# Mutation tests for RandomChords: each run copies the sources to RandomChords/Mut, plants one wrong
# change, and builds the copy through Audit.lean (which imports everything). Every mutant must FAIL to
# build; the unchanged copy (control) must build. Run from this folder after `lake build`.
cd "${0:A:h}" || exit 1
ok=1
FILES=(Basic Branches OneCircle TwoCircles Moments Centres Corollaries HitProb Remarks Offsets Audit)
copy() {
  rm -rf RandomChords/Mut; mkdir -p RandomChords/Mut
  for f in $FILES; do
    sed -e 's/RandomChords\./RandomChords.Mut./g' RandomChords/$f.lean > RandomChords/Mut/$f.lean
  done
}
build() { nice -n 15 timeout 2400 lake build RandomChords.Mut.Audit >/dev/null 2>&1 }
copy
if build; then echo "control builds"; else echo "CONTROL FAILED"; ok=0; fi
run_mut() {
  name="$1"; file="$2"; expr="$3"
  copy
  cp RandomChords/Mut/$file.lean RandomChords/Mut/$file.orig
  sed -i '' "$expr" RandomChords/Mut/$file.lean
  if cmp -s RandomChords/Mut/$file.lean RandomChords/Mut/$file.orig; then echo "NOT APPLIED: $name"; ok=0; return; fi
  rm RandomChords/Mut/$file.orig
  if build; then echo "MUTANT SURVIVED: $name"; ok=0; else echo "rejected: $name"; fi
}
run_mut "normal of the line not perpendicular"   Basic       's#(sgn d \* -d.2 / len d, sgn d \* d.1 / len d)#(sgn d * d.2 / len d, sgn d * d.1 / len d)#'
run_mut "torus mass twice the square"            Basic       's#^lemma four_mul_volume_sq : 4 \* volume sq#lemma four_mul_volume_sq : 2 * volume sq#'
run_mut "branch theorem: constant c + 1"         Branches    's#Measure.map F volume = c • volume.restrict s ∧#Measure.map F volume = (c + 1) • volume.restrict s ∧#'
run_mut "Lemma 1: law 2 • uniform"               OneCircle   's#Measure.map (angles1 b) volume = (4 : ℝ≥0∞) • volume.restrict sq ∧#Measure.map (angles1 b) volume = (2 : ℝ≥0∞) • volume.restrict sq ∧#'
run_mut "Lemma 1: C at phi + theta"              OneCircle   's#+ (-sgnB η) • ContinuousLinearMap.snd ℝ ℝ ℝ)#+ (sgnB η) • ContinuousLinearMap.snd ℝ ℝ ℝ)#'
run_mut "Lemma 2: dphi/dthetaA uses b"           TwoCircles  's#^def c1 (x : ℝ × ℝ) : ℝ := a \* sin x.1 / gfeet a b D x#def c1 (x : ℝ × ℝ) : ℝ := b * sin x.1 / gfeet a b D x#'
run_mut "Lemma 2: gaps at least 1"               TwoCircles  's#    a \* sin x.1 + b \* sin x.2 ≤ gfeet a b D x := by#    a * sin x.1 + b * sin x.2 + 1 ≤ gfeet a b D x := by#'
run_mut "Lemma 2: contributions sum to 2"        TwoCircles  's#∑ p : Bool × Bool, jac a b D p.1 p.2 x = 4 := by#∑ p : Bool × Bool, jac a b D p.1 p.2 x = 2 := by#'
run_mut "Lemma 2 for overlapping discs"          TwoCircles  's#^theorem lemma2 (ha : 0 < a) (hb : 0 < b) (hD : a + b ≤ D) :#theorem lemma2 (ha : 0 < a) (hb : 0 < b) (hD : a ≤ D) :#'
run_mut "Lemma 3: weights in order only"         Moments     "s#(|w.1| = |w'.1| ∧ |w.2| = |w'.2|) ∨ (|w.1| = |w'.2| ∧ |w.2| = |w'.1|) := by#(|w.1| = |w'.1| ∧ |w.2| = |w'.2|) := by#"
run_mut "Lemma 3: second moment over 4"          Moments     's#∫ x, x \^ 2 ∂(lawW w) = π \^ 2 \* (w.1 \^ 2 + w.2 \^ 2) / 2 := by#∫ x, x ^ 2 ∂(lawW w) = π ^ 2 * (w.1 ^ 2 + w.2 ^ 2) / 4 := by#'
run_mut "(T): weight 1 - mu"                     Centres     's#dAB a b D q o ω = wsum (o / D \* a, -((1 + o / D) \* b))#dAB a b D q o ω = wsum (o / D * a, -((1 - o / D) * b))#'
run_mut "Theorem 4: |QO| = a(a+b)/b"             Centres     '/^theorem theorem4 /,/:= by/s#o = b \* (a + b) / a) := by#o = a * (a + b) / b) := by#'
run_mut "Corollary 5: ab = c^2"                  Corollaries 's#      a \* c = b \^ 2) ∧#      a * b = c ^ 2) ∧#'
run_mut "mirrored Theorem 4: b(a+b)/a"           Corollaries "s#o' = 0 ∨ (D = a + b ∧ o' = a \* (a + b) / b) := by#o' = 0 ∨ (D = a + b ∧ o' = b * (a + b) / a) := by#"
run_mut "Corollary 7: factor 1/pi^2"             HitProb     's#^def Hint (r : ℝ) : ℝ := 2 / π \^ 2#def Hint (r : ℝ) : ℝ := 1 / π ^ 2#'
run_mut "Corollary 7: H decreasing"              HitProb     's#theorem H_strictMonoOn : StrictMonoOn H (Ioi 0)#theorem H_strictMonoOn : StrictAntiOn H (Ioi 0)#'
run_mut "Corollary 7: H tends to 1/2"            HitProb     's#theorem H_tendsto_one : Tendsto H atTop (𝓝 1)#theorem H_tendsto_one : Tendsto H atTop (𝓝 (1 / 2))#'
run_mut "Corollary 8: arccos(2 cos v + 1)"       HitProb     's#arccos (2 \* cos v - 1) := by#arccos (2 * cos v + 1) := by#'
run_mut "(2): 2 a^2 D h"                         Remarks     's#((D \^ 2 - a \^ 2 - b \^ 2) \* (k \^ 2 - h \^ 2) + 2 \* b \^ 2 \* D \* h) / (2 \* D \^ 2) := by#((D ^ 2 - a ^ 2 - b ^ 2) * (k ^ 2 - h ^ 2) + 2 * a ^ 2 * D * h) / (2 * D ^ 2) := by#'
run_mut "example: 1/40"                          Remarks     's#= 1 / 50 := by#= 1 / 40 := by#'
run_mut "concentric: a x_A = a x_B"              Remarks     's#      b \* off (nrm (pt (-0) a ω.1) (pt 0 b ω.2)) (pt 0 b ω.2) (0, 0) b := by#      a * off (nrm (pt (-0) a ω.1) (pt 0 b ω.2)) (pt 0 b ω.2) (0, 0) b := by#'
run_mut "direction: divide by 2D"                Offsets     's#(a \* cos x.1 - b \* cos x.2) / D) := by#(a * cos x.1 - b * cos x.2) / (2 * D)) := by#'
rm -rf RandomChords/Mut .lake/build/lib/lean/RandomChords/Mut .lake/build/ir/RandomChords/Mut
if [[ $ok == 1 ]]; then echo "ALL MUTANTS REJECTED, CONTROL BUILDS"; else echo "FAILURES ABOVE"; exit 1; fi
