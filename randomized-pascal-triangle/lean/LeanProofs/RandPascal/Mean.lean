import LeanProofs.RandPascal.TheoremB
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# The quantity asked for: the expected mean of the first `N` rows

Rows `0, …, N-1` hold `N(N+1)/2` numbers, so the expected arithmetic mean of all of them is
`meanN p N = (∑_{n<N} E[S_n]) / (N(N+1)/2)`. If `E[S_n] ≥ λⁿ` with `λ > 1`, it tends to infinity,
i.e. `L_p = ∞`.
-/

open Finset Filter Topology

namespace RandPascal

/-- Expected arithmetic mean of all numbers in rows `0, …, N-1`. -/
noncomputable def meanN (p : ℝ) (N : ℕ) : ℝ :=
  (∑ n ∈ range N, Exp p n (S (n + 4))) / ((N : ℝ) * (N + 1) / 2)

theorem meanN_tendsto_atTop {p lam : ℝ} (hlam : 1 < lam)
    (h : ∀ n, lam ^ n ≤ Exp p n (S (n + 4))) : Tendsto (meanN p) atTop atTop := by
  have hl0 : 0 < lam := by linarith
  -- `N² / λᴺ → 0⁺`, so `λᴺ / N² → ∞`
  have h0 : Tendsto (fun N : ℕ => (N : ℝ) ^ 2 / lam ^ N) atTop (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨tendsto_pow_const_div_const_pow_of_one_lt 2 hlam, ?_⟩
    filter_upwards [eventually_ge_atTop 1] with N hN
    have : (0 : ℝ) < N := by exact_mod_cast hN
    exact Set.mem_Ioi.2 (div_pos (by positivity) (by positivity))
  have h1 : Tendsto (fun N : ℕ => lam⁻¹ * (lam ^ N / (N : ℝ) ^ 2)) atTop atTop := by
    refine Tendsto.const_mul_atTop (inv_pos.2 hl0) ?_
    have := h0.inv_tendsto_nhdsGT_zero
    refine this.congr fun N => ?_
    simp [inv_div]
  refine tendsto_atTop_mono' atTop ?_ h1
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  -- the sum is at least its last term `λ^(N-1)`
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  have hsum : lam ^ M ≤ ∑ n ∈ range (M + 1), Exp p n (S (n + 4)) := by
    rw [sum_range_succ]
    have : 0 ≤ ∑ n ∈ range M, Exp p n (S (n + 4)) :=
      sum_nonneg fun n _ => (pow_nonneg hl0.le n).trans (h n)
    linarith [h M]
  have hden : 0 < ((M + 1 : ℕ) : ℝ) * ((M + 1 : ℕ) + 1) / 2 := by positivity
  have hden' : ((M + 1 : ℕ) : ℝ) * ((M + 1 : ℕ) + 1) / 2 ≤ ((M + 1 : ℕ) : ℝ) ^ 2 := by
    nlinarith
  unfold meanN
  rw [le_div_iff₀ hden]
  calc lam⁻¹ * (lam ^ (M + 1) / ((M + 1 : ℕ) : ℝ) ^ 2) * (((M + 1 : ℕ) : ℝ) * ((M + 1 : ℕ) + 1) / 2)
      ≤ lam⁻¹ * (lam ^ (M + 1) / ((M + 1 : ℕ) : ℝ) ^ 2) * ((M + 1 : ℕ) : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_left hden' (by positivity)
    _ = lam ^ M := by field_simp; ring
    _ ≤ _ := hsum

/-- **Answer for `p > 1 - 1/√2`:** `L_p = ∞`. -/
theorem meanN_diverges_A {p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1) (h : 2 * p ^ 2 - 4 * p + 1 < 0) :
    Tendsto (meanN p) atTop atTop :=
  meanN_tendsto_atTop (one_lt_lamA hp0.le hp1 h) (theoremA hp0 hp1)

/-- **Answer for `p ≥ 29/125`, given the certified local inequality:** `L_p = ∞`. -/
theorem meanN_diverges_B {p : ℝ} (hp0 : 29 / 125 ≤ p) (hp1 : p ≤ 1)
    (hloc : LocalIneq mainCert p) : Tendsto (meanN p) atTop atTop :=
  meanN_tendsto_atTop (by norm_num) (theoremB hp0 hp1 hloc)

end RandPascal
