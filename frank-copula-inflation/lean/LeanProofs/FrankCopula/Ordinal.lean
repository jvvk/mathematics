import Mathlib

/-!
# Moments of integer-score ordinal variables

`U, V` have uniform margins and joint distribution function `C` (a copula). Cutting at `a₁, …, aₙ` and
`b₁, …, bₘ` gives `X = #{k : U > a k}` and `Y = #{l : V > b l}` (integer scores, up to the shift `+1`, which changes
no covariance). Then
`cov(X, Y) = ∑ₖ ∑ₗ (C(aₖ, bₗ) - aₖ bₗ)` and `var X = ∑ₖ ∑ₗ (min(aₖ, aₗ) - aₖ aₗ)`.
These are the formulas evaluated by the certificate `verify/`.
-/

namespace FrankCopula

open MeasureTheory Finset

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

/-- Number of cut-points strictly below `U ω`. -/
noncomputable def score {n : ℕ} (a : Fin n → ℝ) (U : Ω → ℝ) (ω : Ω) : ℝ :=
  ∑ k, {ω | a k < U ω}.indicator 1 ω

/-- Inclusion-exclusion for the upper orthant. -/
lemma prob_gt_gt (U V : Ω → ℝ) (hU : Measurable U) (hV : Measurable V) (a b : ℝ) :
    μ.real ({ω | a < U ω} ∩ {ω | b < V ω}) =
      1 - μ.real {ω | U ω ≤ a} - μ.real {ω | V ω ≤ b} + μ.real ({ω | U ω ≤ a} ∩ {ω | V ω ≤ b}) := by
  have hA : MeasurableSet {ω | U ω ≤ a} := measurableSet_le hU measurable_const
  have hB : MeasurableSet {ω | V ω ≤ b} := measurableSet_le hV measurable_const
  have e : {ω | a < U ω} ∩ {ω | b < V ω} = ({ω | U ω ≤ a} ∪ {ω | V ω ≤ b})ᶜ := by
    ext ω; simp [not_le]
  rw [e, measureReal_compl (hA.union hB), probReal_univ]
  have := measureReal_union_add_inter (μ := μ) (s := {ω | U ω ≤ a}) hB
  linarith

lemma integral_score {n : ℕ} (a : Fin n → ℝ) (U : Ω → ℝ) (hU : Measurable U) :
    ∫ ω, score a U ω ∂μ = ∑ k, μ.real {ω | a k < U ω} := by
  unfold score
  rw [integral_finsetSum _ fun k _ => (integrable_const 1).indicator (measurableSet_lt measurable_const hU)]
  exact sum_congr rfl fun k _ => integral_indicator_one (measurableSet_lt measurable_const hU)

lemma integral_score_mul {n m : ℕ} (a : Fin n → ℝ) (b : Fin m → ℝ) (U V : Ω → ℝ) (hU : Measurable U)
    (hV : Measurable V) :
    ∫ ω, score a U ω * score b V ω ∂μ = ∑ k, ∑ l, μ.real ({ω | a k < U ω} ∩ {ω | b l < V ω}) := by
  have hm : ∀ k l, MeasurableSet ({ω | a k < U ω} ∩ {ω | b l < V ω}) := fun k l =>
    (measurableSet_lt measurable_const hU).inter (measurableSet_lt measurable_const hV)
  have e : (fun ω => score a U ω * score b V ω) =
      fun ω => ∑ k, ∑ l, ({ω | a k < U ω} ∩ {ω | b l < V ω}).indicator 1 ω := by
    funext ω; unfold score; rw [sum_mul_sum]
    refine sum_congr rfl fun k _ => sum_congr rfl fun l _ => ?_
    rw [Set.inter_indicator_one]; rfl
  rw [e, integral_finsetSum _ fun k _ => integrable_finsetSum _ fun l _ =>
    (integrable_const 1).indicator (hm k l)]
  refine sum_congr rfl fun k _ => ?_
  rw [integral_finsetSum _ fun l _ => (integrable_const 1).indicator (hm k l)]
  exact sum_congr rfl fun l _ => integral_indicator_one (hm k l)

/-- **Covariance of integer-score ordinal variables.** -/
theorem cov_score {n m : ℕ} (a : Fin n → ℝ) (b : Fin m → ℝ) (U V : Ω → ℝ) (hU : Measurable U)
    (hV : Measurable V) (C : ℝ → ℝ → ℝ)
    (hUa : ∀ k, μ.real {ω | U ω ≤ a k} = a k) (hVb : ∀ l, μ.real {ω | V ω ≤ b l} = b l)
    (hC : ∀ k l, μ.real ({ω | U ω ≤ a k} ∩ {ω | V ω ≤ b l}) = C (a k) (b l)) :
    ∫ ω, score a U ω * score b V ω ∂μ - (∫ ω, score a U ω ∂μ) * (∫ ω, score b V ω ∂μ) =
      ∑ k, ∑ l, (C (a k) (b l) - a k * b l) := by
  rw [integral_score_mul μ a b U V hU hV, integral_score μ a U hU, integral_score μ b V hV, sum_mul_sum,
    ← sum_sub_distrib]
  refine sum_congr rfl fun k _ => ?_
  rw [← sum_sub_distrib]
  refine sum_congr rfl fun l _ => ?_
  have hk : μ.real {ω | a k < U ω} = 1 - a k := by
    have e : {ω | a k < U ω} = {ω | U ω ≤ a k}ᶜ := by ext; simp [not_le]
    rw [e, measureReal_compl (measurableSet_le hU measurable_const), probReal_univ, hUa]
  have hl : μ.real {ω | b l < V ω} = 1 - b l := by
    have e : {ω | b l < V ω} = {ω | V ω ≤ b l}ᶜ := by ext; simp [not_le]
    rw [e, measureReal_compl (measurableSet_le hV measurable_const), probReal_univ, hVb]
  rw [prob_gt_gt μ U V hU hV, hUa, hVb, hC, hk, hl]; ring

/-- **Variance of an integer-score ordinal variable** with uniform `U`. -/
theorem var_score {n : ℕ} (a : Fin n → ℝ) (U : Ω → ℝ) (hU : Measurable U)
    (hUa : ∀ k, μ.real {ω | U ω ≤ a k} = a k) :
    ∫ ω, score a U ω * score a U ω ∂μ - (∫ ω, score a U ω ∂μ) ^ 2 =
      ∑ k, ∑ l, (min (a k) (a l) - a k * a l) := by
  rw [sq]
  refine cov_score μ a a U U hU hU min hUa hUa fun k l => ?_
  have : {ω | U ω ≤ a k} ∩ {ω | U ω ≤ a l} = {ω | U ω ≤ min (a k) (a l)} := by ext ω; simp
  rw [this]
  rcases le_total (a k) (a l) with h | h
  · rw [min_eq_left h, hUa]
  · rw [min_eq_right h, hUa]

end FrankCopula
