import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic

/-!
# Tangent circles: the integral `∫ cos η / √(cos² s - sin² η) dη = π` (Section 3)

For `|s| < π/2` put `e = π/2 - |s|`. On `|η| < e` we have `|sin η| < cos s`, and
`u(η) = arcsin (sin η / cos s)` has derivative `cos η / √(cos² s - sin² η) > 0`.
At the ends `u = ±π/2`, so the (improper) integral over `(-e, e)` is `π`. This is the step
that makes the crossing angle uniform.
-/

open Real Set intervalIntegral MeasureTheory

namespace TangentCircles

/-- The substitution `u = arcsin (sin η / cos s)`. -/
noncomputable def u (s η : ℝ) : ℝ := Real.arcsin (Real.sin η / Real.cos s)

/-- The integrand. -/
noncomputable def g (s η : ℝ) : ℝ := Real.cos η / Real.sqrt (Real.cos s ^ 2 - Real.sin η ^ 2)

section
variable {s : ℝ} (hs : |s| < π / 2)
include hs

lemma cos_s_pos : 0 < Real.cos s := by
  have := abs_lt.1 hs
  exact Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩

lemma sin_lt_cos {η : ℝ} (hη : |η| < π / 2 - |s|) : |Real.sin η| < Real.cos s := by
  have hs0 := abs_nonneg s
  have habs : |Real.sin η| = Real.sin |η| := by
    have := abs_lt.1 hη
    rcases le_total 0 η with h | h
    · rw [abs_of_nonneg h, abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi h (by linarith))]
    · rw [abs_of_nonpos h, abs_of_nonpos (Real.sin_nonpos_of_nonpos_of_neg_pi_le h (by linarith)),
        Real.sin_neg]
  rw [habs, ← Real.cos_abs s, ← Real.sin_pi_div_two_sub]
  exact Real.sin_lt_sin_of_lt_of_le_pi_div_two (by linarith [abs_nonneg η, Real.pi_pos])
    (by linarith) hη

lemma hasDerivAt_u {η : ℝ} (hη : |η| < π / 2 - |s|) : HasDerivAt (u s) (g s η) η := by
  have hc := cos_s_pos hs
  have hlt := sin_lt_cos hs hη
  have hx : |Real.sin η / Real.cos s| < 1 := by
    rw [abs_div, abs_of_pos hc, div_lt_one hc]; exact hlt
  have h1 : Real.sin η / Real.cos s ≠ -1 := fun h => by rw [h] at hx; norm_num at hx
  have h2 : Real.sin η / Real.cos s ≠ 1 := fun h => by rw [h] at hx; norm_num at hx
  have hd := (Real.hasDerivAt_arcsin h1 h2).comp η ((Real.hasDerivAt_sin η).div_const (Real.cos s))
  have hu : u s = (Real.arcsin ∘ fun x => Real.sin x / Real.cos s) := rfl
  rw [hu]
  convert hd using 1
  -- 1 / √(1 - (sin η / cos s)²) * (cos η / cos s) = cos η / √(cos² s - sin² η)
  have hpos : 0 < Real.cos s ^ 2 - Real.sin η ^ 2 := by
    have := abs_lt.1 hlt
    nlinarith [sq_abs (Real.sin η)]
  have e : 1 - (Real.sin η / Real.cos s) ^ 2 =
      (Real.cos s ^ 2 - Real.sin η ^ 2) / Real.cos s ^ 2 := by
    field_simp
  rw [e, Real.sqrt_div' _ (by positivity), Real.sqrt_sq hc.le]
  unfold g
  field_simp

omit hs in
lemma g_nonneg {η : ℝ} (hη : |η| < π / 2 - |s|) : 0 ≤ g s η := by
  unfold g
  have := abs_lt.1 hη
  have : 0 ≤ Real.cos η := Real.cos_nonneg_of_neg_pi_div_two_le_of_le (by linarith [abs_nonneg s])
    (by linarith [abs_nonneg s])
  positivity

/-- The integral is `π`. -/
theorem integral_g : ∫ η in -(π / 2 - |s|)..(π / 2 - |s|), g s η = π := by
  set e := π / 2 - |s|
  have he : 0 < e := by simp only [e]; linarith
  have hc := cos_s_pos hs
  have mem : ∀ η ∈ Ioo (-e) e, |η| < e := fun η hη => abs_lt.2 ⟨hη.1, hη.2⟩
  have hcont : ContinuousOn (u s) (Icc (-e) e) :=
    (Real.continuous_arcsin.comp (Real.continuous_sin.div_const _)).continuousOn
  have hderiv : ∀ η ∈ Ioo (-e) e, HasDerivAt (u s) (g s η) η :=
    fun η hη => hasDerivAt_u hs (mem η hη)
  have hint : IntervalIntegrable (g s) volume (-e) e := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith)]
    exact integrableOn_deriv_of_nonneg hcont hderiv (fun η hη => g_nonneg (mem η hη))
  rw [integral_eq_sub_of_hasDerivAt_of_le (by linarith) hcont hderiv hint]
  have hse : Real.sin e = Real.cos s := by
    simp only [e]; rw [Real.sin_pi_div_two_sub, Real.cos_abs]
  unfold u
  rw [Real.sin_neg, hse, neg_div, div_self hc.ne', Real.arcsin_one, Real.arcsin_neg,
    Real.arcsin_one]
  ring

end

end TangentCircles
