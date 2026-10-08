/-
  Part F. The growth rate: `f n ^ (1/n) → 4`, answering Stanley's question (MathOverflow 486548).
  Squeeze between `(4^(n-1) / (2n))^(1/n)` and `(4^(n-1))^(1/n)`, both of which tend to `4`.
-/
import LeanProofs.Stanley.Count
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

namespace Stanley

open Filter Topology

/-- `(n-1)/n → 1`, written as `↑(n-1) * (1/n)`. -/
theorem tendsto_pred_div : Tendsto (fun n : ℕ => ((n - 1 : ℕ) : ℝ) * (1 / (n : ℝ))) atTop (𝓝 1) := by
  have h : Tendsto (fun n : ℕ => (1 : ℝ) - 1 / (n : ℝ)) atTop (𝓝 1) := by
    have := tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ)
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub this
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  rw [Nat.cast_sub hn, Nat.cast_one]
  field_simp

/-- `4^((n-1)/n) → 4`. -/
theorem tendsto_upper :
    Tendsto (fun n : ℕ => ((4 : ℝ) ^ (n - 1)) ^ (1 / (n : ℝ))) atTop (𝓝 4) := by
  have hc : Continuous (fun x : ℝ => (4 : ℝ) ^ x) := Real.continuous_const_rpow (by norm_num)
  have := (hc.tendsto 1).comp tendsto_pred_div
  simp only [Real.rpow_one] at this
  refine this.congr' (Eventually.of_forall fun n => ?_)
  simp only [Function.comp_apply]
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]

/-- `(2n)^(1/n) → 1`. -/
theorem tendsto_two_mul_root :
    Tendsto (fun n : ℕ => (2 * (n : ℝ)) ^ (1 / (n : ℝ))) atTop (𝓝 1) := by
  have h2 : Tendsto (fun n : ℕ => (2 : ℝ) ^ (1 / (n : ℝ))) atTop (𝓝 1) := by
    have hc : Continuous (fun x : ℝ => (2 : ℝ) ^ x) := Real.continuous_const_rpow (by norm_num)
    have := (hc.tendsto 0).comp (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ))
    rw [Real.rpow_zero] at this
    exact this
  have hn : Tendsto (fun n : ℕ => (n : ℝ) ^ (1 / (n : ℝ))) atTop (𝓝 1) :=
    tendsto_rpow_div.comp tendsto_natCast_atTop_atTop
  have := h2.mul hn
  rw [mul_one] at this
  refine this.congr' (Eventually.of_forall fun n => ?_)
  show (2 : ℝ) ^ (1 / (n : ℝ)) * (n : ℝ) ^ (1 / (n : ℝ)) = (2 * (n : ℝ)) ^ (1 / (n : ℝ))
  rw [Real.mul_rpow (by norm_num) (Nat.cast_nonneg n)]

/-- `(4^(n-1) / (2n))^(1/n) → 4`. -/
theorem tendsto_lower :
    Tendsto (fun n : ℕ => ((4 : ℝ) ^ (n - 1) / (2 * n)) ^ (1 / (n : ℝ))) atTop (𝓝 4) := by
  have := tendsto_upper.div tendsto_two_mul_root (by norm_num)
  rw [div_one] at this
  refine this.congr' (Eventually.of_forall fun n => ?_)
  show ((4 : ℝ) ^ (n - 1)) ^ (1 / (n : ℝ)) / (2 * (n : ℝ)) ^ (1 / (n : ℝ)) =
    ((4 : ℝ) ^ (n - 1) / (2 * n)) ^ (1 / (n : ℝ))
  rw [Real.div_rpow (by positivity) (by positivity)]

/-- **Stanley's growth rate.** `f(n)^(1/n) → 4`. -/
theorem tendsto_f : Tendsto (fun n : ℕ => (f n : ℝ) ^ (1 / (n : ℝ))) atTop (𝓝 4) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_lower tendsto_upper ?_ ?_
  · filter_upwards [eventually_ge_atTop 2] with n hn
    apply Real.rpow_le_rpow (by positivity) _ (by positivity)
    have h := four_pow_le_f hn
    have hR : ((4 : ℝ) ^ (n - 1)) ≤ 2 * (n : ℝ) * (f n : ℝ) := by
      have : ((4 ^ (n - 1) : ℕ) : ℝ) ≤ ((2 * (n - 1) * f n : ℕ) : ℝ) := by exact_mod_cast h
      push_cast at this
      have hle : ((n - 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast Nat.sub_le n 1
      calc (4 : ℝ) ^ (n - 1) ≤ 2 * ((n - 1 : ℕ) : ℝ) * f n := by
            simpa [Nat.cast_sub (show 1 ≤ n by omega)] using this
        _ ≤ 2 * (n : ℝ) * f n := by gcongr
    rw [div_le_iff₀ (by positivity)]
    linarith
  · filter_upwards with n
    apply Real.rpow_le_rpow (Nat.cast_nonneg _) _ (by positivity)
    exact_mod_cast f_le n

end Stanley
