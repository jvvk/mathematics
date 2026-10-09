#!/bin/zsh
# Mutation tests for SymmetricRatio: each mutant copies one source file, plants a single wrong change,
# and compiles the copy against the original modules. Every mutant must FAIL; the unchanged copies
# (controls) must compile. Run from this folder after `lake build`.
cd "${0:A:h}" || exit 1
M=SymmetricRatio/Mut.lean
ok=1
compile() { nice -n 15 timeout 600 lake env lean "$M" >/dev/null 2>&1 }
for f in Basic Roots Convex Main Bridge; do
  cp "SymmetricRatio/$f.lean" "$M"
  if compile; then echo "control compiles: $f"; else echo "CONTROL FAILED: $f"; ok=0; fi
done
run_mut() {
  name="$1"; file="$2"; expr="$3"
  sed -e "$expr" "SymmetricRatio/$file" > "$M"
  if cmp -s "$M" "SymmetricRatio/$file"; then echo "NOT APPLIED: $name"; ok=0; return; fi
  if compile; then echo "MUTANT SURVIVED: $name"; ok=0; else echo "rejected: $name"; fi
}
run_mut "final: StrictAntiOn"            Bridge.lean 's/    StrictMonoOn (fun x => h n ℓ i x/    StrictAntiOn (fun x => h n ℓ i x/'
run_mut "final: on (0, oo)"              Bridge.lean 's/(h n ℓ (i + 1) x \* h n ℓ (i - 1) x)) (Set.Ioi 1)/(h n ℓ (i + 1) x * h n ℓ (i - 1) x)) (Set.Ioi 0)/'
run_mut "final: cube not square"         Bridge.lean 's/StrictMonoOn (fun x => h n ℓ i x ^ 2/StrictMonoOn (fun x => h n ℓ i x ^ 3/'
run_mut "final: allow i = 0"             Bridge.lean 's/(hℓ : 1 ≤ ℓ) (hi : 1 ≤ i) (hin/(hℓ : 1 ≤ ℓ) (hi : 0 ≤ i) (hin/'
run_mut "vec: x's first, ones last"      Bridge.lean 's/fun j => if (j : ℕ) < p then 1 else x/fun j => if (j : ℕ) < p then x else 1/'
run_mut "Hf: choose index off by one"    Bridge.lean 's/(((p + q + ℓ - 1).choose (ℓ - k)/(((p + q + ℓ).choose (ℓ - k)/'
run_mut "HP_deriv: (l+2) for (l+1)"      Main.lean   's/      C ((ℓ : ℝ) + 1) \* HP N (ℓ + 1) t - C ((N : ℝ) + ℓ + 1) \* HP N ℓ t := by/      C ((ℓ : ℝ) + 2) * HP N (ℓ + 1) t - C ((N : ℝ) + ℓ + 1) * HP N ℓ t := by/'
run_mut "P_rec: (N+l+2) for (N+l+1)"     Basic.lean  's/        - C ((1 + y) \* ((N : ℝ) + ℓ + 1)) \* P N y ℓ := by/        - C ((1 + y) * ((N : ℝ) + ℓ + 2)) * P N y ℓ := by/'
run_mut "W_rec: 2y P^2"                  Basic.lean  's/      C y \* P N y (ℓ + 1) ^ 2 + C ((1 + y)/      C (2 * y) * P N y (ℓ + 1) ^ 2 + C ((1 + y)/'
run_mut "convexity at t >= 0"            Convex.lean 's/(ℓ : ℕ) {t : ℝ} (ht : 1 ≤ t) :/(ℓ : ℕ) {t : ℝ} (ht : 0 ≤ t) :/'
run_mut "roots nonnegative claimed"      Roots.lean  's/      (∀ j < ℓ, r j < 0) := by/      (∀ j < ℓ, 0 < r j) := by/'
rm -f "$M"
if [[ $ok == 1 ]]; then echo "ALL MUTANTS REJECTED, CONTROLS COMPILE"; else echo "FAILURES ABOVE"; exit 1; fi
