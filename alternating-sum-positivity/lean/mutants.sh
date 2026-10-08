#!/bin/zsh
# Mutation tests for AlternatingSum: each mutant copies one source file, plants a single wrong
# change, and compiles the copy against the original earlier modules. Every mutant must FAIL; the
# unchanged copies (controls) must compile, so a failure means the change was caught.
# Run from this folder after `lake build`.
cd "${0:A:h}" || exit 1
D=AlternatingSum
M=$D/Mutant.lean
ok=1
compile() { nice -n 15 timeout 1200 lake env lean "$M" >/dev/null 2>&1 }
control() {
  cp "$D/$1.lean" "$M"
  if compile; then echo "control compiles: $1"; else echo "CONTROL FAILED: $1"; ok=0; fi
}
run_mut() {
  name="$1"; file="$2"; expr="$3"
  cp "$D/$file.lean" "$M"
  sed -i '' "$expr" "$M"
  if cmp -s "$D/$file.lean" "$M"; then echo "NOT APPLIED: $name"; ok=0; return; fi
  if compile; then echo "MUTANT SURVIVED: $name"; ok=0; else echo "rejected: $name"; fi
}
for f in Leibniz Step1 Series Main Coeffs Corollaries Positivity Taylor Binomial Hucht; do control $f; done
run_mut "Leibniz: shift x+r -> x+r+1" Leibniz 's/D (n - r) f (x + r) := by/D (n - r) f (x + r + 1) := by/'
run_mut "Step 3: drop the alternating sign" Leibniz '/^theorem step3/,/^theorem/s/∑ p ∈ range (ν + 1), (-1 : ℚ) ^ p/∑ p ∈ range (ν + 1), (1 : ℚ) ^ p/'
run_mut "L: prefactor (u+a+b-n+1)!" Step1 's/((u + a + b - n) ! : ℚ) \* ∑ i ∈ range (n + 1)/((u + a + b - n + 1) ! : ℚ) * ∑ i ∈ range (n + 1)/'
run_mut "L: numerator (k+l+1)!" Step1 's/\* (k + l) ! \* (a + b - k - l) !/* (k + l + 1) ! * (a + b - k - l) !/'
run_mut "R with (1+z)^2" Series 's/noncomputable def E : PS := (1 - X 1) ^ 2 - X 0 ^ 2/noncomputable def E : PS := (1 + X 1) ^ 2 - X 0 ^ 2/'
run_mut "Theorem 1: R^u instead of R^(u+1)" Main 's/coeff (mono a b) (R ^ (u + 1) \* (R - 1) ^ (a + b - n))/coeff (mono a b) (R ^ u * (R - 1) ^ (a + b - n))/'
run_mut "Theorem 1: prefactor not squared" Main 's/L u a b n = ((u + (a + b - n)) ! : ℚ) ^ 2/L u a b n = ((u + (a + b - n)) ! : ℚ) ^ 1/'
run_mut "Theorem 1: (R-1)^(nu+1)" Main 's/(R - 1) ^ (a + b - n)) := by/(R - 1) ^ (a + b - n + 1)) := by/'
run_mut "coefficients of R^(m+1): 2m+x+2" Coeffs 's/((2 \* m + x + 1 + y).choose (2 \* m + x + 1) : ℚ)/((2 * m + x + 2 + y).choose (2 * m + x + 2) : ℚ)/'
run_mut "extreme case: C(u+a/2+1, a/2)" Corollaries 's/((u + a \/ 2).choose (a \/ 2) : ℚ) := by/((u + a \/ 2 + 1).choose (a \/ 2) : ℚ) := by/'
run_mut "G > 0 (false for odd a)" Corollaries 's/(N : ℝ) (hN : 1 ≤ N) : 0 ≤ Gmom u a b N/(N : ℝ) (hN : 1 ≤ N) : 0 < Gmom u a b N/'
run_mut "positivity: a < 2n" Positivity 's/0 < L u a b n ↔ Even a ∧ a ≤ 2 \* n/0 < L u a b n ↔ Even a ∧ a < 2 * n/'
run_mut "Taylor: degree n - a/2 + 1" Taylor 's/(Even a → a ≤ 2 \* n → P.natDegree = n - a \/ 2)/(Even a → a ≤ 2 * n → P.natDegree = n - a \/ 2 + 1)/'
run_mut "Taylor inner sum: 2^(2d-b+1)" Binomial 's/(-1) ^ (b - d) \* 2 ^ (2 \* d - b) \* (d.choose (2 \* d - b) : ℚ)/(-1) ^ (b - d) * 2 ^ (2 * d - b + 1) * (d.choose (2 * d - b) : ℚ)/'
run_mut "Taylor formula: m < n only" Binomial 's/∑ m ∈ range (n + 1), (u.choose m : ℚ) \* Tinner a b n m := by/∑ m ∈ range n, (u.choose m : ℚ) * Tinner a b n m := by/'
run_mut "Hucht: 2^(b+1)" Hucht 's/Tinner a b n m = 2 ^ b \* ((a \/ 2 + b).choose b : ℚ)/Tinner a b n m = 2 ^ (b + 1) * ((a \/ 2 + b).choose b : ℚ)/'
run_mut "Hucht: parameter (2-b)/2" Hucht 's/  ∑ t ∈ range (j + 1), qrise ((1 - b) \/ 2) t/  ∑ t ∈ range (j + 1), qrise ((2 - b) \/ 2) t/'
rm -f "$M"
if [[ $ok == 1 ]]; then echo "ALL MUTANTS REJECTED, ALL CONTROLS COMPILE"; else echo "FAILURES ABOVE"; exit 1; fi
