import EnclosingCopy.Enclosing.RegularGeom
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.Topology.Order.Lattice

/-!
# The area of the regular `q`-gon of inradius 1 is `q tan (π/q)`

Section 7 uses `area P = q tan (π/q)` for `P = {C : C · uⱼ ≤ 1 for all j}`. We prove it in polar
coordinates. In direction `θ` the point `r (cos θ, sin θ)` has `C · uⱼ = r cos (θ - 2πj/q)`, so the
ray meets `P` in `(0, 1/M(θ)]` with `M(θ) = maxⱼ cos (θ - 2πj/q)`. The function `M` has period
`2π/q` and equals `cos θ` on `[-π/q, π/q]` (`M_eq_cos`, from
`cos θ - cos (θ - 2a) = 2 sin a sin (a - θ) ≥ 0` for `a = πj/q`). Hence
`area P = ∫_{-π}^{π} 1/(2 M²) = q ∫_{-π/q}^{π/q} sec² θ / 2 = q tan (π/q)`.

With this, `segment_term_full`: the segment term of Theorem 8 for every regular `2r`-gon is
`8/(3q²)` with no geometric input left.
-/

namespace Enclosing

open MeasureTheory Set Real

variable {q : ℕ}

/-- `M(θ) = maxⱼ cos (θ - 2πj/q)`. -/
noncomputable def Mq (q : ℕ) [NeZero q] (θ : ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty fun j : Fin q => cos (θ - 2 * π * j / q)

/-- The key inequality: on `[-π/q, π/q]` the side `j = 0` is the outermost. -/
lemma cos_le_cos_on_period (hq : 2 ≤ q) {θ : ℝ} (hθ : |θ| ≤ π / q) (j : Fin q) :
    cos (θ - 2 * π * j / q) ≤ cos θ := by
  have hq' : (0 : ℝ) < q := by positivity
  set a : ℝ := π * j / q with ha
  have hcs : cos θ - cos (θ - 2 * π * j / q) = 2 * sin a * sin (a - θ) := by
    rw [cos_sub_cos]
    have e1 : (θ + (θ - 2 * π * j / q)) / 2 = -(a - θ) := by rw [ha]; ring
    have e2 : (θ - (θ - 2 * π * j / q)) / 2 = a := by rw [ha]; ring
    rw [e1, e2, sin_neg]; ring
  have hj : (j : ℝ) ≤ q - 1 := by
    have : (j : ℕ) + 1 ≤ q := j.isLt
    have : ((j : ℕ) : ℝ) + 1 ≤ q := by exact_mod_cast this
    linarith
  have hθ' := abs_le.1 hθ
  have hsa : 0 ≤ sin a := by
    apply sin_nonneg_of_nonneg_of_le_pi (by positivity)
    rw [ha, div_le_iff₀ hq']; nlinarith [pi_pos]
  rcases Nat.eq_zero_or_pos (j : ℕ) with h0 | hpos
  · have : a = 0 := by rw [ha, h0]; simp
    rw [this, sin_zero] at hcs; linarith
  · have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast hpos
    have hlow : 0 ≤ a - θ := by
      have : π / q ≤ a := by rw [ha]; apply div_le_div_of_nonneg_right _ hq'.le; nlinarith [pi_pos]
      linarith
    have hup : a - θ ≤ π := by
      have : a ≤ π - π / q := by
        rw [ha, show π - π / q = π * (q - 1) / q by field_simp]
        apply div_le_div_of_nonneg_right _ hq'.le; nlinarith [pi_pos]
      linarith
    have := sin_nonneg_of_nonneg_of_le_pi hlow hup
    nlinarith

lemma Mq_eq_cos [NeZero q] (hq : 2 ≤ q) {θ : ℝ} (hθ : |θ| ≤ π / q) : Mq q θ = cos θ := by
  apply le_antisymm
  · exact Finset.sup'_le _ _ fun j _ => cos_le_cos_on_period hq hθ j
  · exact Finset.le_sup'_of_le _ (Finset.mem_univ 0) (by simp)

/-- Every integer index gives a term below `M`: reduce it mod `q`. -/
lemma cos_le_Mq [NeZero q] (θ : ℝ) (m : ℤ) : cos (θ - 2 * π * m / q) ≤ Mq q θ := by
  have hq0 : (0 : ℤ) < q := by have := NeZero.pos q; exact_mod_cast this
  have hr0 : 0 ≤ m % q := Int.emod_nonneg _ hq0.ne'
  have hrq : m % q < q := Int.emod_lt_of_pos _ hq0
  let k : Fin q := ⟨(m % q).toNat, by omega⟩
  refine Finset.le_sup'_of_le _ (Finset.mem_univ k) (le_of_eq ?_)
  have hk : ((k : ℕ) : ℝ) = ((m % q : ℤ) : ℝ) := by
    simp only [k]; exact_mod_cast Int.toNat_of_nonneg hr0
  have hm : (m : ℝ) = ((m % q : ℤ) : ℝ) + q * ((m / q : ℤ) : ℝ) := by
    exact_mod_cast (Int.emod_add_mul_ediv m q).symm
  have hq' : (q : ℝ) ≠ 0 := by have := NeZero.ne q; exact_mod_cast this
  rw [hk, hm, ← cos_sub_int_mul_two_pi (θ - 2 * π * ((m % q : ℤ) : ℝ) / q) (m / q)]
  congr 1
  field_simp
  ring

lemma Mq_periodic [NeZero q] : Function.Periodic (Mq q) (2 * π / q) := by
  intro θ
  have hq' : (q : ℝ) ≠ 0 := by have := NeZero.ne q; exact_mod_cast this
  apply le_antisymm
  · refine Finset.sup'_le _ _ fun j _ => ?_
    have := cos_le_Mq (q := q) θ (((j : ℕ) : ℤ) - 1)
    convert this using 2
    push_cast; field_simp; ring
  · refine Finset.sup'_le _ _ fun j _ => ?_
    have := cos_le_Mq (q := q) (θ + 2 * π / q) (((j : ℕ) : ℤ) + 1)
    convert this using 2
    push_cast; field_simp; ring

lemma Mq_cont [NeZero q] : Continuous (Mq q) := by
  unfold Mq
  exact Continuous.finset_sup'_apply _ fun j _ => by fun_prop

lemma Mq_pos [NeZero q] (hq : 3 ≤ q) (θ : ℝ) : 0 < Mq q θ := by
  have hq' : (0 : ℝ) < q := by positivity
  have hq3 : (3 : ℝ) ≤ q := by exact_mod_cast hq
  set T := 2 * π / q with hT
  have hTpos : 0 < T := by positivity
  set n : ℤ := ⌊(θ + π / q) / T⌋
  have h1 := Int.floor_le ((θ + π / q) / T)
  have h2 := Int.lt_floor_add_one ((θ + π / q) / T)
  rw [le_div_iff₀ hTpos] at h1
  rw [div_lt_iff₀ hTpos] at h2
  rw [← Mq_periodic.sub_int_mul_eq n, Mq_eq_cos (by omega)]
  · apply cos_pos_of_mem_Ioo
    have hpq : π / q < π / 2 := by
      apply div_lt_div_of_pos_left pi_pos (by norm_num) (by linarith)
    have : T = 2 * (π / q) := by rw [hT]; ring
    constructor <;> nlinarith
  · have : T = 2 * (π / q) := by rw [hT]; ring
    rw [abs_le]; constructor <;> nlinarith

/-- The ray in direction `θ` meets `P` in `(0, 1/M(θ)]`. -/
lemma ray_mem_P [NeZero q] {r θ : ℝ} (hr : 0 < r) :
    (r * cos θ, r * sin θ) ∈ Preg q ↔ r * Mq q θ ≤ 1 := by
  have hdot : ∀ j : Fin q, dot (r * cos θ, r * sin θ) (un q j) = r * cos (θ - 2 * π * j / q) := by
    intro j; simp only [dot, un, cos_sub]; ring
  simp only [Preg, mem_setOf_eq, hdot]
  constructor
  · intro h
    obtain ⟨k, -, hk⟩ := Finset.exists_mem_eq_sup' (Finset.univ_nonempty (α := Fin q))
      fun j : Fin q => cos (θ - 2 * π * j / q)
    rw [Mq, hk]; exact h k
  · intro h j
    calc r * cos (θ - 2 * π * j / q) ≤ r * Mq q θ :=
          mul_le_mul_of_nonneg_left (Finset.le_sup' (fun j : Fin q => cos (θ - 2 * π * j / q))
            (Finset.mem_univ j)) hr.le
      _ ≤ 1 := h

lemma measurableSet_Preg : MeasurableSet (Preg q) := by
  have : Preg q = ⋂ j : Fin q, {C : ℝ × ℝ | dot C (un q j) ≤ 1} := by ext; simp [Preg]
  rw [this]
  exact MeasurableSet.iInter fun j =>
    measurableSet_le (by unfold dot; fun_prop) measurable_const

/-- The radial integral: `∫_{r > 0, r M ≤ 1} r dr = 1/(2 M²)`. -/
lemma radial [NeZero q] (hq : 3 ≤ q) (θ : ℝ) :
    ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal r * (Preg q).indicator 1 (r * cos θ, r * sin θ)
      = ENNReal.ofReal (1 / (2 * Mq q θ ^ 2)) := by
  have hM := Mq_pos hq θ
  have hcongr : ∀ r ∈ Ioi (0 : ℝ), ENNReal.ofReal r * (Preg q).indicator 1 (r * cos θ, r * sin θ)
      = (Iic (1 / Mq q θ)).indicator (fun r => ENNReal.ofReal r) r := by
    intro r hr
    by_cases h : r * Mq q θ ≤ 1
    · have h' : r ∈ Iic (1 / Mq q θ) := by
        rw [mem_Iic, le_div_iff₀ hM]; exact h
      rw [indicator_of_mem ((ray_mem_P hr).2 h), indicator_of_mem h']; simp
    · have h' : r ∉ Iic (1 / Mq q θ) := by
        rw [mem_Iic, le_div_iff₀ hM]; exact h
      rw [indicator_of_notMem (fun hP => h ((ray_mem_P hr).1 hP)), indicator_of_notMem h']
      simp
  rw [setLIntegral_congr_fun measurableSet_Ioi hcongr, lintegral_indicator measurableSet_Iic,
    Measure.restrict_restrict measurableSet_Iic, Iic_inter_Ioi]
  rw [← ofReal_integral_eq_lintegral_ofReal]
  · congr 1
    rw [integral_Ioc_eq_integral_Ioo, ← integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le (by positivity), integral_id]
    field_simp
    ring
  · exact (continuous_id.integrableOn_Icc).mono_set Ioc_subset_Icc_self
  · exact (ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall fun r hr => hr.1.le)

/-- `∫_{-a}^{a} 1/(2 cos² θ) = tan a` for `0 ≤ a < π/2`. -/
lemma integral_half_sec_sq {a : ℝ} (ha : 0 ≤ a) (ha' : a < π / 2) :
    ∫ θ in (-a)..a, 1 / (2 * cos θ ^ 2) = tan a := by
  have hcos : ∀ x ∈ uIcc (-a) a, cos x ≠ 0 := by
    intro x hx
    rw [uIcc_of_le (by linarith)] at hx
    exact (cos_pos_of_mem_Ioo ⟨by linarith [hx.1], by linarith [hx.2]⟩).ne'
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun x => tan x / 2)]
  · simp only [tan_neg]; ring
  · intro x hx
    have := (hasDerivAt_tan (hcos x hx)).div_const 2
    convert this using 1; field_simp
  · apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.div continuousOn_const (by fun_prop)
    intro x hx; have := hcos x hx; positivity

lemma halfInvSq_cont [NeZero q] (hq : 3 ≤ q) : Continuous fun θ => 1 / (2 * Mq q θ ^ 2) :=
  continuous_const.div ((Mq_cont.pow 2).const_mul 2) fun θ => by
    have := Mq_pos hq θ; positivity

/-- **The angular integral**: `∫_{-π}^{π} 1/(2 M²) = q tan (π/q)`. -/
lemma angular [NeZero q] (hq : 3 ≤ q) :
    ∫ θ in (-π)..π, 1 / (2 * Mq q θ ^ 2) = q * tan (π / q) := by
  have hq' : (0 : ℝ) < q := by positivity
  have hq3 : (3 : ℝ) ≤ q := by exact_mod_cast hq
  have hg : Function.Periodic (fun θ => 1 / (2 * Mq q θ ^ 2)) (2 * π / q) := fun θ => by
    show 1 / (2 * Mq q (θ + 2 * π / q) ^ 2) = 1 / (2 * Mq q θ ^ 2)
    rw [Mq_periodic θ]
  have hcont : Continuous fun θ => 1 / (2 * Mq q θ ^ 2) :=
    continuous_const.div ((Mq_cont.pow 2).const_mul 2) fun θ => by
      have := Mq_pos hq θ; positivity
  have hint : ∀ a b, IntervalIntegrable (fun θ => 1 / (2 * Mq q θ ^ 2)) volume a b :=
    fun a b => hcont.intervalIntegrable a b
  have hπ : π = -π + (q : ℤ) • (2 * π / q) := by
    rw [zsmul_eq_mul]; push_cast; field_simp; ring
  have hshift : -(π / q) + 2 * π / q = π / q := by field_simp; ring
  have hpq : π / q < π / 2 := div_lt_div_of_pos_left pi_pos (by norm_num) (by linarith)
  have hle : -(π / q) ≤ π / q := by have : 0 ≤ π / q := by positivity
                                    linarith
  have hEq : EqOn (fun θ => 1 / (2 * Mq q θ ^ 2)) (fun θ => 1 / (2 * cos θ ^ 2))
      (uIcc (-(π / q)) (π / q)) := by
    intro θ hθ
    rw [uIcc_of_le hle] at hθ
    simp only
    rw [Mq_eq_cos (by omega) (abs_le.2 hθ)]
  calc ∫ θ in (-π)..π, 1 / (2 * Mq q θ ^ 2)
      = ∫ θ in (-π)..(-π + (q : ℤ) • (2 * π / q)), 1 / (2 * Mq q θ ^ 2) := by rw [← hπ]
    _ = (q : ℤ) • ∫ θ in (-π)..(-π + 2 * π / q), 1 / (2 * Mq q θ ^ 2) :=
        hg.intervalIntegral_add_zsmul_eq (q : ℤ) (-π) hint
    _ = (q : ℤ) • ∫ θ in (-(π / q))..(π / q), 1 / (2 * Mq q θ ^ 2) := by
        rw [hg.intervalIntegral_add_eq (-π) (-(π / q)), hshift]
    _ = q * tan (π / q) := by
        rw [intervalIntegral.integral_congr hEq, integral_half_sec_sq (by positivity) hpq,
          zsmul_eq_mul]
        push_cast; ring

/-- **The area of the regular `q`-gon of inradius 1 is `q tan (π/q)`.** -/
theorem volume_Preg [NeZero q] (hq : 3 ≤ q) :
    volume (Preg q) = ENNReal.ofReal (q * tan (π / q)) := by
  rw [← lintegral_indicator_one measurableSet_Preg, ← lintegral_comp_polarCoord_symm]
  simp only [polarCoord_symm_apply, polarCoord_target, smul_eq_mul]
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict, lintegral_prod_symm]
  · simp_rw [radial hq]
    rw [← ofReal_integral_eq_lintegral_ofReal, ← integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le (by linarith [pi_pos]), angular hq]
    · exact ((halfInvSq_cont hq).integrableOn_Icc).mono_set Ioo_subset_Icc_self
    · exact Filter.Eventually.of_forall fun θ => by have := Mq_pos hq θ; positivity
  · apply Measurable.aemeasurable
    apply Measurable.mul (ENNReal.measurable_ofReal.comp measurable_fst)
    exact (measurable_one.indicator measurableSet_Preg).comp (by fun_prop)

/-- **The segment term of Theorem 8 for every regular `2r`-gon (`r ≥ 2`) is `8/(3q²)`**, now with
no geometric input. -/
theorem segment_term_full {r : ℕ} (hr : 2 ≤ r) :
    let q : ℝ := 2 * r
    let S : ℝ := ∑ j ∈ Finset.Ico 1 r, 2 * sin (2 * π * j / q)
    q * (∫ x in (-1 : ℝ)..1, ∫ s₁ in (-1 : ℝ)..x, ∫ s₂ in x..1, (s₂ - s₁)) *
        (2 * (∫ Θ, ∫ t in Ioi |Θ|, exp (-(2 * q * t)) *
            (volume ((fun C : ℝ × ℝ => C.1) '' Rreg (2 * r) t Θ)).toReal)
          + 2 * S * ∫ Θ, ∫ t in Ioi |Θ|, exp (-(2 * q * t)) * (volume (Rreg (2 * r) t Θ)).toReal)
      = 8 / (3 * q ^ 2) := by
  have : NeZero (2 * r) := ⟨by omega⟩
  apply segment_term_measure hr
  rw [volume_Preg (by omega), ENNReal.toReal_ofReal]
  · push_cast; ring_nf
  · have h2 : (2 : ℝ) ≤ r := by exact_mod_cast hr
    have h4 : (4 : ℝ) ≤ ((2 * r : ℕ) : ℝ) := by push_cast; linarith
    have : 0 < ((2 * r : ℕ) : ℝ) := by linarith
    have : 0 ≤ tan (π / ((2 * r : ℕ) : ℝ)) := by
      apply tan_nonneg_of_nonneg_of_le_pi_div_two (by positivity)
      rw [div_le_div_iff₀ this (by norm_num)]; nlinarith [pi_pos]
    positivity

/-- **The vertex-term integral for every regular `q`-gon:** `∫∫ e^{-2qt} area R = tan(π/q)/(4q³)`. -/
theorem V_regular_full [NeZero q] (hq : 3 ≤ q) :
    ∫ Θ, ∫ t in Ioi |Θ|, exp (-(2 * q * t)) * (volume (Rreg q t Θ)).toReal
      = q * tan (π / q) / (4 * (q : ℝ) ^ 4) := by
  rw [V_regular q (by omega), volume_Preg hq, ENNReal.toReal_ofReal]
  have hq' : (3 : ℝ) ≤ q := by exact_mod_cast hq
  have : 0 ≤ tan (π / q) := by
    apply tan_nonneg_of_nonneg_of_le_pi_div_two (by positivity)
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]; nlinarith [pi_pos]
  positivity

end Enclosing
