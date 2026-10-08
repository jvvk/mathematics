#!/bin/bash
# Mutation tests for the Lean formalisation of this paper.
# Each mutant must FAIL to compile. Usage: scripts/mutants.sh [index ...], run from lean/ after lake build. Indices follow the development project; mutants on modules not in this folder were removed.
cd "$(dirname "$0")/.." || exit 1
S="${TMPDIR:-/tmp}/stanley_density_mut"; mkdir -p "$S"
pass=0; total=0; idx=0
want() { [ $# -eq 0 ] && return 0; for k in "${SEL[@]}"; do [ "$k" = "$idx" ] && return 0; done; return 1; }
SEL=("$@")
mutate() {  # file  old  new  label
  idx=$((idx+1))
  if [ ${#SEL[@]} -gt 0 ] && ! want "${SEL[@]}"; then return; fi
  local f="$1" old="$2" new="$3" label="$4"
  total=$((total+1))
  cp "$f" "$S/orig.lean"
  OLD="$old" NEW="$new" F="$f" python3 - <<'PY'
import os
from pathlib import Path
p = Path(os.environ["F"]); s = p.read_text()
assert os.environ["OLD"] in s, "mutation target not found"
p.write_text(s.replace(os.environ["OLD"], os.environ["NEW"], 1))
PY
  if nice -n 15 timeout 900 lake env lean --threads=1 "$f" 2>&1 | grep -q "error"; then
    echo "KILLED   [$idx] $label"; pass=$((pass+1))
  else
    echo "SURVIVED [$idx] $label"
  fi
  cp "$S/orig.lean" "$f"
}
mutate LeanProofs/Stanley/Growth.lean "else (some (r - 1), some (r - 1), false))" \
  "else (some r, some (r - 1), false))" "growth rule: asymmetric doubled-row case"
mutate LeanProofs/Stanley/Growth.lean "g.col (i + 1) < g.col i ↔ u i < u (i + 1)" \
  "g.col (i + 1) < g.col i ↔ u (i + 1) < u i" "column descents reversed"
mutate LeanProofs/Stanley/Fill.lean "(fun q => 2 ≤ q ∧ q - 1 ∈ X ∧ q - 2 ∉ X ∧ m ≤ q ∧ 2 ≤ rk X q)" \
  "(fun q => 2 ≤ q ∧ q - 1 ∈ X ∧ m ≤ q ∧ 2 ≤ rk X q)" "two-started runs without the long-predecessor rule"
mutate LeanProofs/Stanley/Fill.lean "def exL (p : ℕ) : ℕ := if rk X p = 1 then 1 else rk X p" \
  "def exL (p : ℕ) : ℕ := if rk X p = 1 then 1 else rk X p + 1" "leg letters skip a row"
mutate LeanProofs/Stanley/Density.lean "|stG m x - stG m y| ≤ 2 * hammingDist x y" \
  "|stG m x - stG m y| ≤ 1 * hammingDist x y" "G claimed 1-Lipschitz"
mutate LeanProofs/Stanley/Density.lean "(4 : ℝ) ^ (n - 1) - f n ≤ 6 * Real.exp" \
  "(4 : ℝ) ^ (n - 1) - f n ≤ 5 * Real.exp" "density constant 5 instead of 6"
mutate LeanProofs/Stanley/Density.lean "      3 * (2 ^ (n - 1) * Real.exp (-(n : ℝ) / 20000)) := by" \
  "      2 * (2 ^ (n - 1) * Real.exp (-(n : ℝ) / 20000)) := by" "bad points: 2 slow tails instead of 3"
mutate LeanProofs/Stanley/Density.lean "theorem exp_absorb {n : ℝ} (hn : 6000 ≤ n) :" \
  "theorem exp_absorb {n : ℝ} (hn : 1000 ≤ n) :" "fast tails absorbed from n = 1000"
mutate_build() {  # file  old  new  label  module: mutant must break `lake build module`
  idx=$((idx+1))
  if [ ${#SEL[@]} -gt 0 ] && ! want "${SEL[@]}"; then return; fi
  local f="$1" old="$2" new="$3" label="$4" mod="$5"
  total=$((total+1))
  cp "$f" "$S/orig.lean"
  OLD="$old" NEW="$new" F="$f" python3 - <<'PY'
import os
from pathlib import Path
p = Path(os.environ["F"]); s = p.read_text()
assert os.environ["OLD"] in s, "mutation target not found"
p.write_text(s.replace(os.environ["OLD"], os.environ["NEW"], 1))
PY
  if nice -n 15 timeout 1500 lake build "$mod" 2>&1 | grep -q "error"; then
    echo "KILLED   [$idx] $label"; pass=$((pass+1))
  else
    echo "SURVIVED [$idx] $label"
  fi
  cp "$S/orig.lean" "$f"
  nice -n 15 timeout 1500 lake build "$mod" >/dev/null 2>&1
}
# Theorem 2 (Alternating.lean, AltChecks.lean)
mutate LeanProofs/Stanley/Alternating.lean "1 - Real.pi ^ 4 / (48 * n)| ≤ C / (n : ℝ) ^ 2 := by
  set C0" "1 - Real.pi ^ 4 / (24 * n)| ≤ C / (n : ℝ) ^ 2 := by
  set C0" "Theorem 2 with pi^4/24 instead of pi^4/48"
mutate LeanProofs/Stanley/Alternating.lean "theorem cc_two (m : ℕ) : cc (m + 2) m = (m : ℝ) / 3 + if Odd m then 0 else 1 / 2" \
  "theorem cc_two (m : ℕ) : cc (m + 2) m = (m : ℝ) / 3 + if Odd m then 0 else 1 / 3" "c_{n,n-2} with 1/3 for 1/2"
mutate LeanProofs/Stanley/Alternating.lean "theorem σ_close {m : ℕ} (hm : 1 ≤ m) : |σ m - 1| ≤ 3 / 2 / 3 ^ m" \
  "theorem σ_close {m : ℕ} (hm : 1 ≤ m) : |σ m - 1| ≤ 1 / 2 / 3 ^ m" "sigma bound too strong"
mutate LeanProofs/Stanley/Alternating.lean "a m = 4 * m ! * σ m ^ 2 / r ^ (m + 1) := by" \
  "a m = 2 * m ! * σ m ^ 2 / r ^ (m + 1) := by" "a_m formula with 2 for 4"
mutate_build LeanProofs/Stanley/AltBasic.lean "(E m : ℝ) / m ! = 2 * (2 / Real.pi) ^ (m + 1) * σ m" \
  "(E m : ℝ) / m ! = (2 / Real.pi) ^ (m + 1) * σ m" "Euler formula missing factor 2 (all-index theorem)" LeanProofs.Stanley.AltChecks
mutate_build LeanProofs/Stanley/AltBasic.lean "coeff n (if Odd m then u ^ m else s * u ^ m)" \
  "coeff n (if Even m then u ^ m else s * u ^ m)" "Stanley GF selector swapped (non-vacuity check)" LeanProofs.Stanley.AltChecks
# Stanley GF (DoubleCoset, Atoms, PermCycles, PermCount, StanleyProof)
mutate LeanProofs/Stanley/DoubleCoset.lean "jointSubsetCount n A B = Nat.card (FQ n A B)" \
  "jointSubsetCount n A B + 1 = Nat.card (FQ n A B)" "descent pairs = orbits plus one"
mutate LeanProofs/Stanley/Atoms.lean "Φ (ext c d) = (if Even (∑ a, c a) then 1 else 0) * Φ c" \
  "Φ (ext c d) = (if Odd (∑ a, c a) then 1 else 0) * Φ c" "even-atom factor with the wrong parity"
mutate LeanProofs/Stanley/PermCount.lean "    | some none => some (some (τ d))
    | some (some a) => if a = d then none else some (some (τ a))" \
  "    | some none => some (some (τ d))
    | some (some a) => if a = d then some none else some (some (τ a))" "splice sends d to the wrong new point"
mutate LeanProofs/Stanley/PermCount.lean "(Fintype.card α + 1) * ((if all then 1 else 0) + Fintype.card α) * Qc α all m" \
  "(Fintype.card α + 1) * ((if all then 1 else 0) + Fintype.card α + 1) * Qc α all m" "recurrence coefficient off by one"
mutate LeanProofs/Stanley/PermCycles.lean "      then (E (univ.filter (fun q : cyc w => Odd (len w q))).card : ℤ) ^ 2 else 0 := by
  have : Nonempty" \
  "      then (E (univ.filter (fun q : cyc w => Odd (len w q))).card : ℤ) ^ 2 + 1 else 0 := by
  have : Nonempty" "Foulkes value off by one"
mutate LeanProofs/Stanley/StanleyProof.lean "theorem oddC_le {n : ℕ} (w : Perm (Fin n)) : oddC w ≤ n := by" \
  "theorem oddC_le {n : ℕ} (w : Perm (Fin n)) : oddC w < n := by" "odd cycles strictly fewer than points"
# Singleton criterion, singleton counts, dominance necessity (2026-10-08)
mutate LeanProofs/Stanley/TwoBlocks.lean "(⟨i, by omega⟩ : Fin n) ∉ A ∧ (⟨i+1,h⟩ : Fin n) ∈ A" \
  "(⟨i, by omega⟩ : Fin n) ∈ A ∧ (⟨i+1,h⟩ : Fin n) ∉ A" "rises read as falls"
mutate LeanProofs/Stanley/DominanceNecessity.lean "∑ j : Fin (n+1), min R.card (fib (blk n B) j)" \
  "∑ j : Fin (n+1), min (R.card-1) (fib (blk n B) j)" "Gale-Ryser bound with |R|-1"
mutate LeanProofs/Stanley/LowerGap.lean "theorem f_add_le (n : ℕ) : f n + (2 ^ (n - 1) - 1) ≤ 4 ^ (n - 1) := by" \
  "theorem f_add_le (n : ℕ) : f n + 2 ^ (n - 1) ≤ 4 ^ (n - 1) := by" "gap counts T = empty as well"
mutate LeanProofs/Stanley/LowerGap.lean "((2 : ℝ) ^ (n - 1) - 1) / 4 ^ (n - 1) ≤ 1 - (f n : ℝ) / 4 ^ (n - 1)" \
  "((2 : ℝ) ^ n - 1) / 4 ^ (n - 1) ≤ 1 - (f n : ℝ) / 4 ^ (n - 1)" "gap rate 2^n instead of 2^(n-1)"
# Lemma 2.1 converse by forward growth diagrams (2026-10-08)
mutate LeanProofs/Stanley/GrowthForward.lean "if r = s then (some (r + 1), some (r + 1)) else" \
  "if r = s then (some r, some r) else" "forward rule does not bump to the next row"
mutate LeanProofs/Stanley/GrowthForward.lean "  | _, _, true => (some 0, some 0)" \
  "  | _, _, true => (some 1, some 1)" "cross starts a box in row 1"
mutate LeanProofs/Stanley/GrowthForward.lean "decide (i < n ∧ wf w i = j)" \
  "decide (j < n ∧ wf w j = i)" "crosses of the inverse permutation"
mutate LeanProofs/Stanley/GrowthForward.lean "(∀ r, cnt u n r = cnt v n r) ∧ asc n u = S ∧ asc n v = T := by" \
  "(∀ r, cnt u n r = cnt v n r) ∧ asc n u = S ∧ asc n u = T := by" "both descent sets read from one tableau"
# Block obstruction and f(n) <= 4^(n-1) - 3^(n-1) + 1 (2026-10-08)
mutate LeanProofs/Stanley/BlockObstruction.lean "(hT : ∀ j ≤ S.card, i + j ∈ T) : (S, T) ∉ pairs n" \
  "(hT : ∀ j < S.card, i + j ∈ T) : (S, T) ∉ pairs n" "block of |S| instead of |S|+1"
mutate LeanProofs/Stanley/BlockObstruction.lean "    (h : w ⟨b, hb⟩ < w ⟨a, by omega⟩) : ∃ q ∈ descP w, a ≤ q ∧ q < b := by" \
  "    (h : w ⟨b, hb⟩ < w ⟨a, by omega⟩) : ∃ q ∈ descP w, a < q ∧ q < b := by" "descent strictly inside the interval"
mutate LeanProofs/Stanley/BlockObstruction.lean "theorem f_add_three_pow_le (n : ℕ) : f n + (3 ^ (n - 1) - 1) ≤ 4 ^ (n - 1) := by" \
  "theorem f_add_three_pow_le (n : ℕ) : f n + 3 ^ (n - 1) ≤ 4 ^ (n - 1) := by" "gap 3^(n-1) without the -1"
# Theorem 1 with rate 1/150 (DensitySharp, 2026-10-08)
mutate LeanProofs/Stanley/DensitySharp.lean "    1 - (f n : ℝ) / 4 ^ (n - 1) ≤ 6 * Real.exp (-(n : ℝ) / 150) := by" \
  "    1 - (f n : ℝ) / 4 ^ (n - 1) ≤ 6 * Real.exp (-(n : ℝ) / 140) := by" "rate 1/140 claimed"
mutate LeanProofs/Stanley/DensitySharp.lean "    (chg m K X).card ≤ 2 * (ups m K X).card + 1 := by" \
  "    (chg m K X).card ≤ 2 * (ups m K X).card := by" "changes at most 2G (drops the +1)"
mutate LeanProofs/Stanley/DensitySharp.lean "  fun i => if m + 1 ≤ i.1 then xor (ω i) (ω (prev i)) else ω i" \
  "  fun i => if m + 1 ≤ i.1 then (ω i) && (ω (prev i)) else ω i" "change map uses and instead of xor"
mutate LeanProofs/Stanley/DensitySharp.lean "    (hdiff : |(S.card : ℝ) - T.card| ≤ n / 12) : (S, T) ∈ pairs n := by" \
  "    (hdiff : |(S.card : ℝ) - T.card| ≤ n / 6) : (S, T) ∈ pairs n := by" "size gap n/6 instead of n/12"
# Theorem 3.6: the Gale-Ryser obstruction has rate log(4/3) (GaleRyserRate, 2026-10-08)
mutate LeanProofs/Stanley/GaleRyserRate.lean "    (bigBlocks n j y).card * 2 ^ y ≤ (n.choose j) ^ 2 * 2 ^ (n - 1) := by" \
  "    (bigBlocks n j y).card * 2 ^ y ≤ n.choose j * 2 ^ (n - 1) := by" "union bound with C(n,j) instead of C(n,j)^2"
mutate LeanProofs/Stanley/GaleRyserRate.lean "  (range n).filter (fun i => block A i ∈ R ∧ (i + 1 = n ∨ i ∈ A))" \
  "  (range n).filter (fun i => block A i ∈ R ∧ i ∈ A)" "last positions miss the final block"
mutate LeanProofs/Stanley/GaleRyserRate.lean "    A.card + 1 ≤ ((range (n + 1)).filter (fun j => 0 < blen n A j)).card := by" \
  "    A.card + 2 ≤ ((range (n + 1)).filter (fun j => 0 < blen n A j)).card := by" "|A|+2 nonempty blocks claimed"
mutate LeanProofs/Stanley/GaleRyserRate.lean "      ∃ k ∈ Ioo m n, ∃ e ∈ Icc 1 n, A.card + 2 ≤ k + e ∧ e ≤ excess n B k := by" \
  "      ∃ k ∈ Ioo m n, ∃ e ∈ Icc 1 n, A.card + 3 ≤ k + e ∧ e ≤ excess n B k := by" "large regime claims r <= k+e-2"
mutate LeanProofs/Stanley/GaleRyserRate.lean "      4 * n ^ 2 * 2 ^ (n - 1) * (1 / 2) ^ (k + e) := by" \
  "      2 * n ^ 2 * 2 ^ (n - 1) * (1 / 2) ^ (k + e) := by" "tail of E_k with 2n^2 instead of 4n^2"
mutate LeanProofs/Stanley/GaleRyserRate.lean "    (h : range (S.card + 1) ⊆ T) : ¬ RunDominance n S (complementCuts n T) := by" \
  "    (h : range S.card ⊆ T) : ¬ RunDominance n S (complementCuts n T) := by" "block of |S| violates (3.2)"
mutate LeanProofs/Stanley/GaleRyserRate.lean "      (4 * n ^ 3 + 2 ^ (Nat.clog 2 (n ^ 2) + 1 - 1) *" \
  "      (2 * n ^ 3 + 2 ^ (Nat.clog 2 (n ^ 2) + 1 - 1) *" "upper bound with 2n^3 instead of 4n^3"
mutate LeanProofs/Stanley/GaleRyserRate.lean "    ((3 : ℝ) ^ (n - 1) - 1) / 4 ^ (n - 1) ≤ (grBad n).card / 4 ^ (n - 1) ∧" \
  "    ((3 : ℝ) ^ (n - 1)) / 4 ^ (n - 1) ≤ (grBad n).card / 4 ^ (n - 1) ∧" "lower bound without the -1"
mutate LeanProofs/Stanley/GaleRyserRate.lean "    (3 / 4 : ℝ) ^ (n + 1) ≤ (grBad n).card / 4 ^ (n - 1) ∧" \
  "    (3 / 4 : ℝ) ^ n ≤ (grBad n).card / 4 ^ (n - 1) ∧" "asymptotic lower bound (3/4)^n"
mutate LeanProofs/Stanley/GaleRyserRate.lean "    1 - (Stanley.f n : ℝ) / 4 ^ (n - 1) = (grBad n).card / 4 ^ (n - 1) := by" \
  "    1 - (Stanley.f n : ℝ) / 4 ^ (n - 1) = 2 * (grBad n).card / 4 ^ (n - 1) := by" "Corollary 3.7 counts failures twice"
echo "$pass / $total mutants killed"
