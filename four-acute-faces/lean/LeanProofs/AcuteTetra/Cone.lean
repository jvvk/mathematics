import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Acute tetrahedron: the volume of a cone in the unit ball (Archimedes, by slices)

In `ℝ³ = ℝ × ℝ²`, for `0 ≤ t ≤ 1` the cone `{y : ‖y‖ < 1, t‖y‖ ≤ y₀}` (and its strict version)
has volume `(2π/3)(1 - t)`. Slicing at height `z` gives a disc of area `π·min(1 - z², z²(1-t²)/t²)`
(the whole disc `π(1 - z²)` when `t = 0`); integrating over `0 < z < 1` gives the result. This is
Archimedes' hat-box theorem in the form the paper uses (Section 6).
-/

namespace AcuteTetra

open MeasureTheory Real Set Metric

abbrev E3 := EuclideanSpace ℝ (Fin 3)
abbrev E2 := EuclideanSpace ℝ (Fin 2)

/-- `y ↦ (y₀, (y₁, y₂))`. -/
noncomputable def split (y : E3) : ℝ × E2 := (y 0, WithLp.toLp 2 fun j => y j.succ)

lemma split_mp : MeasurePreserving split (volume : Measure E3) ((volume : Measure ℝ).prod volume) := by
  have h1 := PiLp.volume_preserving_ofLp (Fin 3)
  have h2 := volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) 0
  have h3 := (MeasurePreserving.id (volume : Measure ℝ)).prod (PiLp.volume_preserving_toLp (Fin 2))
  have := h3.comp (h2.comp h1)
  convert this using 1
  funext y
  rfl

lemma norm_sq_split (y : E3) : ‖y‖ ^ 2 = (split y).1 ^ 2 + ‖(split y).2‖ ^ 2 := by
  simp [split, EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_succ]

/-- Discs: `‖w‖ < R` and `‖w‖ ≤ ρ` (or `< ρ`) has area `π·min(R, ρ)²`. -/
lemma vol_disc_inter (R ρ : ℝ) (hR : 0 ≤ R) (hρ : 0 ≤ ρ) (strict : Bool) :
    volume {w : E2 | ‖w‖ < R ∧ (if strict then ‖w‖ < ρ else ‖w‖ ≤ ρ)} =
      ENNReal.ofReal (π * min R ρ ^ 2) := by
  have hpi := pi_pos.le
  rcases le_or_gt R ρ with h | h
  · have : {w : E2 | ‖w‖ < R ∧ (if strict then ‖w‖ < ρ else ‖w‖ ≤ ρ)} = ball 0 R := by
      ext w
      simp only [mem_ofPred_eq, mem_ball_zero_iff]
      refine ⟨fun hw => hw.1, fun hw => ⟨hw, ?_⟩⟩
      cases strict
      · simp only [Bool.false_eq_true, ite_false]; linarith
      · simp only [ite_true]; linarith
    rw [this, EuclideanSpace.volume_ball_fin_two, min_eq_left h, ← ENNReal.ofReal_pow hR,
      ← ENNReal.ofReal_mul (by positivity), mul_comm]
  · cases strict
    · have : {w : E2 | ‖w‖ < R ∧ (if false then ‖w‖ < ρ else ‖w‖ ≤ ρ)} = closedBall 0 ρ := by
        ext w
        simp only [mem_ofPred_eq, mem_closedBall_zero_iff, Bool.false_eq_true, ite_false]
        exact ⟨fun hw => hw.2, fun hw => ⟨lt_of_le_of_lt hw h, hw⟩⟩
      rw [this, EuclideanSpace.volume_closedBall_fin_two, min_eq_right h.le, ← ENNReal.ofReal_pow hρ,
        ← ENNReal.ofReal_mul (by positivity), mul_comm]
    · have : {w : E2 | ‖w‖ < R ∧ (if true then ‖w‖ < ρ else ‖w‖ ≤ ρ)} = ball 0 ρ := by
        ext w
        simp only [mem_ofPred_eq, mem_ball_zero_iff, ite_true]
        exact ⟨fun hw => hw.2, fun hw => ⟨lt_trans hw h, hw⟩⟩
      rw [this, EuclideanSpace.volume_ball_fin_two, min_eq_right h.le, ← ENNReal.ofReal_pow hρ,
        ← ENNReal.ofReal_mul (by positivity), mul_comm]

/-- The cone `{y : ‖y‖ < 1, t‖y‖ ≤ y₀}` (or `<`). -/
def cone (t : ℝ) (strict : Bool) : Set E3 :=
  {y | ‖y‖ < 1 ∧ (if strict then t * ‖y‖ < y 0 else t * ‖y‖ ≤ y 0)}

/-- The same cone in the coordinates `ℝ × ℝ²`. -/
def coneT (t : ℝ) (strict : Bool) : Set (ℝ × E2) :=
  {p | √(p.1 ^ 2 + ‖p.2‖ ^ 2) < 1 ∧
    (if strict then t * √(p.1 ^ 2 + ‖p.2‖ ^ 2) < p.1 else t * √(p.1 ^ 2 + ‖p.2‖ ^ 2) ≤ p.1)}

lemma cone_eq (t : ℝ) (strict : Bool) : cone t strict = split ⁻¹' coneT t strict := by
  ext y
  have h : ‖y‖ = √((split y).1 ^ 2 + ‖(split y).2‖ ^ 2) := by
    rw [← norm_sq_split, Real.sqrt_sq (norm_nonneg _)]
  simp only [cone, coneT, mem_ofPred_eq, mem_preimage, ← h]
  rfl

lemma coneT_meas (t : ℝ) (strict : Bool) : MeasurableSet (coneT t strict) := by
  have hc : Continuous fun p : ℝ × E2 => √(p.1 ^ 2 + ‖p.2‖ ^ 2) := by fun_prop
  cases strict
  · exact (measurableSet_lt hc.measurable measurable_const).inter
      (measurableSet_le (hc.measurable.const_mul t) measurable_fst)
  · exact (measurableSet_lt hc.measurable measurable_const).inter
      (measurableSet_lt (hc.measurable.const_mul t) measurable_fst)

/-- Radius of the cone's cross-section at height `z`. -/
noncomputable def rho (t z : ℝ) : ℝ := if t = 0 then 1 else z * √(1 - t ^ 2) / t

/-- Area of the cross-section at height `z`. -/
noncomputable def area (t z : ℝ) : ℝ := π * min (√(1 - z ^ 2)) (rho t z) ^ 2

lemma slice_eq (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (strict : Bool) (z : ℝ) (hz0 : 0 < z)
    (hz1 : z < 1) :
    Prod.mk z ⁻¹' coneT t strict =
      {w : E2 | ‖w‖ < √(1 - z ^ 2) ∧ (if strict then ‖w‖ < rho t z else ‖w‖ ≤ rho t z)} := by
  ext w
  simp only [coneT, mem_preimage, mem_ofPred_eq]
  set r := ‖w‖ with hr
  have hr0 : 0 ≤ r := norm_nonneg w
  set S := √(z ^ 2 + r ^ 2) with hS
  have hS0 : 0 ≤ S := Real.sqrt_nonneg _
  have hS2 : S ^ 2 = z ^ 2 + r ^ 2 := Real.sq_sqrt (by positivity)
  have hR : S < 1 ↔ r < √(1 - z ^ 2) := by
    rw [Real.lt_sqrt hr0]
    constructor
    · intro h; nlinarith
    · intro h; nlinarith
  rw [hR]
  rcases eq_or_lt_of_le ht0 with h0 | h0
  · subst h0
    simp only [rho, ite_true, zero_mul]
    have h1 : √(1 - z ^ 2) ≤ 1 := by
      rw [Real.sqrt_le_one]; nlinarith
    cases strict <;> simp only [Bool.false_eq_true, ite_false, ite_true] <;>
      constructor <;> intro h <;> refine ⟨h.1, ?_⟩ <;> linarith [h.1]
  · have hρ : rho t z = z * √(1 - t ^ 2) / t := by simp [rho, h0.ne']
    set q := √(1 - t ^ 2) with hq
    have hq0 : 0 ≤ q := Real.sqrt_nonneg _
    have hq2 : q ^ 2 = 1 - t ^ 2 := Real.sq_sqrt (by nlinarith)
    have hρ0 : 0 ≤ rho t z := by rw [hρ]; positivity
    have hρt : rho t z * t = z * q := by rw [hρ]; field_simp
    -- `t S ≤ z ↔ r ≤ ρ`, comparing squares of nonnegative numbers
    have key : t ^ 2 * S ^ 2 - z ^ 2 = t ^ 2 * (r ^ 2 - rho t z ^ 2) := by
      have : (rho t z * t) ^ 2 = z ^ 2 * (1 - t ^ 2) := by rw [hρt, mul_pow, hq2]
      nlinarith
    have htS : 0 ≤ t * S := by positivity
    have ht2 : 0 < t ^ 2 := by positivity
    cases strict
    · simp only [Bool.false_eq_true, ite_false]
      refine and_congr_right fun _ => ?_
      constructor
      · intro h
        have : t ^ 2 * S ^ 2 ≤ z ^ 2 := by nlinarith
        have : r ^ 2 ≤ rho t z ^ 2 := by nlinarith
        nlinarith
      · intro h
        have : r ^ 2 ≤ rho t z ^ 2 := by nlinarith
        have : (t * S) ^ 2 ≤ z ^ 2 := by nlinarith
        nlinarith [sq_nonneg (t * S - z), sq_nonneg (t * S + z)]
    · simp only [ite_true]
      refine and_congr_right fun _ => ?_
      constructor
      · intro h
        have : t ^ 2 * S ^ 2 < z ^ 2 := by nlinarith
        have : r ^ 2 < rho t z ^ 2 := by nlinarith
        nlinarith
      · intro h
        have : r ^ 2 < rho t z ^ 2 := by nlinarith
        have : (t * S) ^ 2 < z ^ 2 := by nlinarith
        nlinarith [sq_nonneg (t * S - z), sq_nonneg (t * S + z)]

lemma slice_vol (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (strict : Bool) (z : ℝ) (hz : z ≠ 0) :
    volume (Prod.mk z ⁻¹' coneT t strict) = (Ioo 0 1).indicator (fun z => ENNReal.ofReal (area t z)) z := by
  by_cases hz' : z ∈ Ioo (0 : ℝ) 1
  · rw [indicator_of_mem hz', slice_eq t ht0 ht1 strict z hz'.1 hz'.2, area]
    have hρ0 : 0 ≤ rho t z := by
      unfold rho; split_ifs
      · norm_num
      · exact div_nonneg (mul_nonneg hz'.1.le (Real.sqrt_nonneg _)) ht0
    exact vol_disc_inter _ _ (Real.sqrt_nonneg _) hρ0 strict
  · rw [indicator_of_notMem hz', measure_eq_zero_iff_ae_notMem]
    refine Filter.Eventually.of_forall fun w hw => ?_
    simp only [coneT, mem_preimage, mem_ofPred_eq] at hw
    have hS : |z| ≤ √(z ^ 2 + ‖w‖ ^ 2) := by
      rw [← Real.sqrt_sq_eq_abs]; exact Real.sqrt_le_sqrt (le_add_of_nonneg_right (sq_nonneg _))
    have htS : 0 ≤ t * √(z ^ 2 + ‖w‖ ^ 2) := mul_nonneg ht0 (Real.sqrt_nonneg _)
    have hzle : t * √(z ^ 2 + ‖w‖ ^ 2) ≤ z := by
      cases strict
      · simpa using hw.2
      · exact (by simpa using hw.2 : _ < z).le
    rcases not_and_or.1 hz' with h | h
    · push Not at h
      rcases lt_or_eq_of_le h with h | h
      · linarith
      · exact hz h
    · push Not at h
      have := le_abs_self z
      linarith [hw.1]

lemma area_cont (t : ℝ) : Continuous (area t) := by
  unfold area rho
  split_ifs <;> fun_prop

lemma area_nonneg (t z : ℝ) : 0 ≤ area t z := by unfold area; positivity

lemma integral_area (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ∫ z in (0 : ℝ)..1, area t z = 2 * π / 3 * (1 - t) := by
  have hI := fun a b => (area_cont t).intervalIntegrable (μ := volume) a b
  rw [← intervalIntegral.integral_add_adjacent_intervals (hI 0 t) (hI t 1)]
  have h2 : ∫ z in t..1, area t z = ∫ z in t..1, π * (1 - z ^ 2) := by
    refine intervalIntegral.integral_congr fun z hz => ?_
    rw [uIcc_of_le ht1] at hz
    have hz1 : 0 ≤ 1 - z ^ 2 := by nlinarith [hz.1, hz.2]
    have hle : √(1 - z ^ 2) ≤ rho t z := by
      unfold rho
      split_ifs with h0
      · rw [Real.sqrt_le_one]; nlinarith
      · have htp : 0 < t := lt_of_le_of_ne ht0 (Ne.symm h0)
        rw [le_div_iff₀ htp]
        have hq : 0 ≤ 1 - t ^ 2 := by nlinarith
        have h1 : √(1 - z ^ 2) * t = √((1 - z ^ 2) * t ^ 2) := by
          rw [Real.sqrt_mul hz1, Real.sqrt_sq ht0]
        have h2 : z * √(1 - t ^ 2) = √(z ^ 2 * (1 - t ^ 2)) := by
          rw [Real.sqrt_mul (sq_nonneg z), Real.sqrt_sq (by linarith [hz.1])]
        rw [h1, h2]
        exact Real.sqrt_le_sqrt (by nlinarith [hz.1])
    simp only [area, min_eq_left hle, Real.sq_sqrt hz1]
  have h1 : ∫ z in (0 : ℝ)..t, area t z = ∫ z in (0 : ℝ)..t, π * (1 - t ^ 2) / t ^ 2 * z ^ 2 := by
    rcases eq_or_lt_of_le ht0 with h0 | h0
    · subst h0; simp
    refine intervalIntegral.integral_congr fun z hz => ?_
    rw [uIcc_of_le ht0] at hz
    have hq : 0 ≤ 1 - t ^ 2 := by nlinarith
    have hρ : rho t z = z * √(1 - t ^ 2) / t := by simp [rho, h0.ne']
    have hle : rho t z ≤ √(1 - z ^ 2) := by
      rw [hρ, div_le_iff₀ h0]
      have h1 : √(1 - z ^ 2) * t = √((1 - z ^ 2) * t ^ 2) := by
        rw [Real.sqrt_mul (by nlinarith [hz.1, hz.2]), Real.sqrt_sq ht0]
      have h2 : z * √(1 - t ^ 2) = √(z ^ 2 * (1 - t ^ 2)) := by
        rw [Real.sqrt_mul (sq_nonneg z), Real.sqrt_sq hz.1]
      rw [h1, h2]
      exact Real.sqrt_le_sqrt (by nlinarith [hz.1, hz.2])
    rw [area, min_eq_right hle, hρ, div_pow, mul_pow, Real.sq_sqrt hq]
    field_simp
  rw [h1, h2, intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_sub intervalIntegrable_const ((continuous_pow 2).intervalIntegrable _ _), integral_pow,
    integral_pow, intervalIntegral.integral_const]
  rcases eq_or_lt_of_le ht0 with h0 | h0
  · subst h0; simp; ring
  · field_simp
    ring

/-- **Archimedes, cone form.** For `0 ≤ t ≤ 1` the cone `{‖y‖ < 1, t‖y‖ ≤ y₀}` (or `<`) has
volume `(2π/3)(1 - t)`. -/
theorem vol_cone (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (strict : Bool) :
    volume (cone t strict) = ENNReal.ofReal (2 * π / 3 * (1 - t)) := by
  rw [cone_eq, split_mp.measure_preimage (coneT_meas t strict).nullMeasurableSet,
    Measure.prod_apply (coneT_meas t strict)]
  have hae : (fun z => volume (Prod.mk z ⁻¹' coneT t strict)) =ᵐ[volume]
      (Ioo 0 1).indicator (fun z => ENNReal.ofReal (area t z)) := by
    filter_upwards [Measure.ae_ne volume 0] with z hz
    exact slice_vol t ht0 ht1 strict z hz
  rw [lintegral_congr_ae hae, lintegral_indicator measurableSet_Ioo,
    ← ofReal_integral_eq_lintegral_ofReal
      ((area_cont t).integrableOn_Icc.mono_set Ioo_subset_Icc_self)
      (Filter.Eventually.of_forall fun z => area_nonneg t z),
    integral_Ioc_eq_integral_Ioo.symm, ← intervalIntegral.integral_of_le zero_le_one,
    integral_area t ht0 ht1]

end AcuteTetra
