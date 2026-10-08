import Mathlib.Analysis.Complex.Liouville
import Mathlib.Tactic

/-!
# Lemniscates: Liouville with square-root growth

The trace of the intersection is an entire function of each level `r` that grows like `√|r|`.
An entire function with sublinear growth is constant; this is the square-root case, proved from
Cauchy's estimate for the derivative on circles of radius `t²`.
-/

namespace Lemniscates

/-- An entire function with `‖f z‖ ≤ A + B √‖z‖` is constant. -/
theorem eq_of_sqrt_growth {f : ℂ → ℂ} (hf : Differentiable ℂ f) {A B : ℝ}
    (hb : ∀ z, ‖f z‖ ≤ A + B * Real.sqrt ‖z‖) (z w : ℂ) : f z = f w := by
  suffices h : ∀ c, deriv f c = 0 from is_const_of_deriv_eq_zero hf h z w
  intro c
  by_contra hne
  set d := ‖deriv f c‖ with hd
  have hdpos : 0 < d := norm_pos_iff.mpr hne
  set K := |A| + 2 * |B| with hK
  have hK0 : 0 ≤ K := by positivity
  set t := max 1 (max (Real.sqrt ‖c‖) (2 * K / d + 1)) with ht
  have ht1 : 1 ≤ t := le_max_left _ _
  have htc : Real.sqrt ‖c‖ ≤ t := le_trans (le_max_left _ _) (le_max_right _ _)
  have htK : 2 * K / d + 1 ≤ t := le_trans (le_max_right _ _) (le_max_right _ _)
  have htpos : 0 < t := by linarith
  have hc : ‖c‖ ≤ t ^ 2 := by
    have := Real.sq_sqrt (norm_nonneg c)
    nlinarith [Real.sqrt_nonneg ‖c‖]
  -- the bound on the circle of radius `t²` about `c`
  have hsphere : ∀ z ∈ Metric.sphere c (t ^ 2), ‖f z‖ ≤ K * t := by
    intro z hz
    rw [mem_sphere_iff_norm] at hz
    have hz2 : ‖z‖ ≤ 2 * t ^ 2 := by
      calc ‖z‖ ≤ ‖c‖ + ‖z - c‖ := by
              have := norm_sub_norm_le z c; linarith
        _ ≤ 2 * t ^ 2 := by rw [hz]; linarith
    have hsq : Real.sqrt ‖z‖ ≤ 2 * t := by
      rw [Real.sqrt_le_left (by positivity)]
      nlinarith
    calc ‖f z‖ ≤ A + B * Real.sqrt ‖z‖ := hb z
      _ ≤ |A| + |B| * Real.sqrt ‖z‖ := by
          have h1 : A ≤ |A| := le_abs_self A
          have h2 : B * Real.sqrt ‖z‖ ≤ |B| * Real.sqrt ‖z‖ :=
            mul_le_mul_of_nonneg_right (le_abs_self B) (Real.sqrt_nonneg _)
          linarith
      _ ≤ |A| * t + |B| * (2 * t) := by
          have h1 : |A| ≤ |A| * t := le_mul_of_one_le_right (abs_nonneg A) ht1
          have h2 : |B| * Real.sqrt ‖z‖ ≤ |B| * (2 * t) :=
            mul_le_mul_of_nonneg_left hsq (abs_nonneg B)
          linarith
      _ = K * t := by rw [hK]; ring
  have hcauchy := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (by positivity)
    hf.diffContOnCl hsphere
  rw [← hd] at hcauchy
  -- `d ≤ K t / t² = K / t ≤ d / 2`, impossible
  have hKt : K * t / t ^ 2 = K / t := by field_simp
  rw [hKt] at hcauchy
  have hlt : K / t ≤ d / 2 := by
    rw [div_le_div_iff₀ htpos (by norm_num)]
    have : 2 * K / d ≤ t := by linarith
    rw [div_le_iff₀ hdpos] at this
    linarith
  linarith

end Lemniscates
