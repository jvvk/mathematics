import EnclosingCopy.Poisson.Mecke
import EnclosingCopy.Enclosing.Void
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# The Poisson limit model (Section 2), truncated at depth `T`

A convex polygon of area one is described by its sides `i : Fin m`: support number `hᵢ`, outward
normal `uᵢ`, and positions `aᵢ < bᵢ` along the side, with the identities (1)
`∑ Lᵢ uᵢ = 0`, `∑ Lᵢ hᵢ = 2`, `∑ (bᵢ² - aᵢ²) = 0` (`Sides`). A point of the model is
`(i, s, D)`: side, position, depth. The model is the Poisson process with intensity Lebesgue
measure on the strips `[aᵢ, bᵢ] × [0, T]` (`Λ T`).

A copy `z = (ε, C, Θ)` has, on side `i`, the line `D = Θ s - Hᵢ` with `Hᵢ = ε hᵢ + C · uᵢ`; a point
violates it if it lies strictly between `D = 0` and the line (`violates`).

`model_void` is Lemma 7 as a probability in the model: on the event
`Hᵢ ≤ min (Θ aᵢ) (Θ bᵢ)`, if the lines stay below the truncation depth, then
`P(no point violates z) = e^{2ε}`.
-/

namespace Enclosing

open MeasureTheory Set Real

/-- Side data of a convex polygon of area one. -/
structure Sides (m : ℕ) where
  h : Fin m → ℝ
  u : Fin m → ℝ × ℝ
  a : Fin m → ℝ
  b : Fin m → ℝ
  hab : ∀ i, a i < b i
  sum_u1 : ∑ i, (b i - a i) * (u i).1 = 0
  sum_u2 : ∑ i, (b i - a i) * (u i).2 = 0
  sum_h : ∑ i, (b i - a i) * h i = 2
  sum_sq : ∑ i, (b i ^ 2 - a i ^ 2) = 0

variable {m : ℕ} (K : Sides m)

/-- A point of the model: side, position, depth. -/
abbrev Pt (m : ℕ) := Fin m × ℝ × ℝ

/-- A copy: `(ε, C, Θ)`. -/
abbrev Copy := ℝ × (ℝ × ℝ) × ℝ

/-- `Hᵢ(z) = ε hᵢ + C · uᵢ`. -/
def Hs (z : Copy) (i : Fin m) : ℝ := z.1 * K.h i + dot z.2.1 (K.u i)

/-- The point `x = (i, s, D)` violates the copy `z`: `D < Θ s - Hᵢ`. -/
def violates (z : Copy) (x : Pt m) : Prop := x.2.2 < z.2.2 * x.2.1 - Hs K z x.1

/-- The copy is feasible for the configuration. -/
def Feasible (μ : Multiset (Pt m)) (z : Copy) : Prop := ∀ x ∈ μ, ¬ violates K z x

/-- The intensity: Lebesgue measure on the strips `[aᵢ, bᵢ] × [0, T]`. -/
noncomputable def Λ (T : ℝ) : Measure (Pt m) :=
  ∑ i, (Measure.dirac i).prod (volume.restrict (Icc (K.a i) (K.b i) ×ˢ Icc 0 T))


lemma strip_finite (i : Fin m) (T : ℝ) :
    volume (Icc (K.a i) (K.b i) ×ˢ Icc (0 : ℝ) T) ≠ ⊤ :=
  (isCompact_Icc.prod isCompact_Icc).measure_lt_top.ne

instance (i : Fin m) (T : ℝ) :
    IsFiniteMeasure (volume.restrict (Icc (K.a i) (K.b i) ×ˢ Icc (0 : ℝ) T)) :=
  isFiniteMeasure_restrict.2 (strip_finite K i T)

instance (T : ℝ) : IsFiniteMeasure (Λ K T) := by
  unfold Λ
  constructor
  rw [Measure.coe_finset_sum, Finset.sum_apply]
  exact ENNReal.sum_lt_top.2 fun i _ => measure_lt_top _ _

/-- The region of points violating the copy `z`. -/
def Vz (z : Copy) : Set (Pt m) := {x | violates K z x}

lemma measurableSet_Vz (z : Copy) : MeasurableSet (Vz K z) := by
  unfold Vz violates
  exact measurableSet_lt (measurable_snd.comp measurable_snd)
    ((measurable_const.mul (measurable_fst.comp measurable_snd)).sub
      ((measurable_of_countable (Hs K z)).comp measurable_fst))

/-- The area of the violation region on one side: `∫_a^b (Θ s - H) ds` when the line is between
`0` and `T`. -/
lemma volume_slice {a b Θ H T : ℝ} (hab : a ≤ b) (hE : H ≤ min (Θ * a) (Θ * b))
    (hT : ∀ s ∈ Icc a b, Θ * s - H ≤ T) :
    volume ((Icc a b ×ˢ Icc (0 : ℝ) T) ∩ {p : ℝ × ℝ | p.2 < Θ * p.1 - H})
      = ENNReal.ofReal (Θ * (b ^ 2 - a ^ 2) / 2 - (b - a) * H) := by
  have hmeas : MeasurableSet ((Icc a b ×ˢ Icc (0 : ℝ) T) ∩ {p : ℝ × ℝ | p.2 < Θ * p.1 - H}) :=
    (measurableSet_Icc.prod measurableSet_Icc).inter
      (measurableSet_lt measurable_snd ((measurable_const.mul measurable_fst).sub measurable_const))
  rw [Measure.volume_eq_prod, Measure.prod_apply hmeas]
  have hsec : ∀ s : ℝ, volume (Prod.mk s ⁻¹' ((Icc a b ×ˢ Icc (0 : ℝ) T) ∩
      {p : ℝ × ℝ | p.2 < Θ * p.1 - H}))
        = (Icc a b).indicator (fun s => ENNReal.ofReal (Θ * s - H)) s := by
    intro s
    by_cases hs : s ∈ Icc a b
    · rw [indicator_of_mem hs]
      have hset : Prod.mk s ⁻¹' ((Icc a b ×ˢ Icc (0 : ℝ) T) ∩ {p : ℝ × ℝ | p.2 < Θ * p.1 - H})
          = Ico 0 (Θ * s - H) := by
        ext D
        simp only [mem_preimage, mem_inter_iff, mem_prod, mem_Icc, mem_setOf_eq, mem_Ico]
        constructor
        · rintro ⟨⟨-, h1, -⟩, h3⟩; exact ⟨h1, h3⟩
        · rintro ⟨h1, h3⟩; exact ⟨⟨hs, h1, (h3.le.trans (hT s hs))⟩, h3⟩
      rw [hset, Real.volume_Ico]
      congr 1; ring
    · rw [indicator_of_notMem hs]
      have hset : Prod.mk s ⁻¹' ((Icc a b ×ˢ Icc (0 : ℝ) T) ∩ {p : ℝ × ℝ | p.2 < Θ * p.1 - H})
          = ∅ := by
        ext D
        simp only [mem_preimage, mem_inter_iff, mem_prod, mem_empty_iff_false, iff_false]
        exact fun h => hs h.1.1
      rw [hset, measure_empty]
  simp_rw [hsec]
  rw [lintegral_indicator measurableSet_Icc, ← ofReal_integral_eq_lintegral_ofReal,
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab, integral_line]
  · exact (by fun_prop : Continuous fun s : ℝ => Θ * s - H).integrableOn_Icc
  · exact (ae_restrict_iff' measurableSet_Icc).2
      (Filter.Eventually.of_forall fun s hs => line_nonneg hE hs)

/-- Identities (1) give `∑ᵢ (Θ (bᵢ² - aᵢ²)/2 - Lᵢ Hᵢ) = -2ε`. -/
lemma sum_line_area (z : Copy) :
    ∑ i, (z.2.2 * (K.b i ^ 2 - K.a i ^ 2) / 2 - (K.b i - K.a i) * Hs K z i) = -(2 * z.1) := by
  have h1 : ∑ i, z.2.2 * (K.b i ^ 2 - K.a i ^ 2) / 2 = 0 := by
    rw [← Finset.sum_div, ← Finset.mul_sum, K.sum_sq]; simp
  have h2 : ∑ i, (K.b i - K.a i) * Hs K z i = 2 * z.1 := by
    simp only [Hs, dot, mul_add, Finset.sum_add_distrib]
    have e1 : ∑ i, (K.b i - K.a i) * (z.1 * K.h i) = z.1 * 2 := by
      rw [← K.sum_h, Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
    have e2 : ∑ i, (K.b i - K.a i) * (z.2.1.1 * (K.u i).1) = 0 := by
      rw [show (0 : ℝ) = z.2.1.1 * 0 by ring, ← K.sum_u1, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    have e3 : ∑ i, (K.b i - K.a i) * (z.2.1.2 * (K.u i).2) = 0 := by
      rw [show (0 : ℝ) = z.2.1.2 * 0 by ring, ← K.sum_u2, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [e1, e2, e3]; ring
  rw [Finset.sum_sub_distrib, h1, h2]; ring

/-- The intensity of the violation region is `-2ε`. -/
lemma Λ_Vz (T : ℝ) (z : Copy) (hE : ∀ i, Hs K z i ≤ min (z.2.2 * K.a i) (z.2.2 * K.b i))
    (hT : ∀ i, ∀ s ∈ Icc (K.a i) (K.b i), z.2.2 * s - Hs K z i ≤ T) :
    Λ K T (Vz K z) = ENNReal.ofReal (-(2 * z.1)) := by
  unfold Λ
  rw [Measure.coe_finset_sum, Finset.sum_apply]
  have hterm : ∀ i, ((Measure.dirac i).prod (volume.restrict (Icc (K.a i) (K.b i) ×ˢ Icc 0 T)))
      (Vz K z) = ENNReal.ofReal (z.2.2 * (K.b i ^ 2 - K.a i ^ 2) / 2
        - (K.b i - K.a i) * Hs K z i) := by
    intro i
    rw [Measure.dirac_prod, Measure.map_apply measurable_prodMk_left (measurableSet_Vz K z),
      Measure.restrict_apply' (measurableSet_Icc.prod measurableSet_Icc), inter_comm]
    exact volume_slice (K.hab i).le (hE i) (hT i)
  simp_rw [hterm]
  rw [← ENNReal.ofReal_sum_of_nonneg fun i _ => line_area_nonneg (K.hab i).le (hE i)]
  congr 1
  exact sum_line_area K z

/-- **Lemma 7 in the model.** On the event `Hᵢ ≤ min (Θ aᵢ) (Θ bᵢ)`, with the lines below the
truncation depth, the probability that no point of the Poisson process violates the copy is
`e^{2ε}`. -/
theorem model_void (T : ℝ) (z : Copy) (hE : ∀ i, Hs K z i ≤ min (z.2.2 * K.a i) (z.2.2 * K.b i))
    (hT : ∀ i, ∀ s ∈ Icc (K.a i) (K.b i), z.2.2 * s - Hs K z i ≤ T) :
    PoissonPP.prob (Λ K T) (fun μ => Feasible K μ z) = ENNReal.ofReal (Real.exp (2 * z.1)) := by
  have hv := PoissonPP.void_prob (Λ K T) (measurableSet_Vz K z)
  have hnn : 0 ≤ -(2 * z.1) := by
    rw [← sum_line_area K z]
    exact Finset.sum_nonneg fun i _ => line_area_nonneg (K.hab i).le (hE i)
  unfold Feasible
  rw [show (fun μ : Multiset (Pt m) => ∀ x ∈ μ, ¬ violates K z x)
      = (fun μ => ∀ x ∈ μ, x ∉ Vz K z) from rfl, hv, Λ_Vz K T z hE hT, ENNReal.toReal_ofReal hnn]
  ring_nf

/-- **Every polygon of area one gives side data** (identities (1) from `Polygon.lean`). -/
noncomputable def Sides.ofPolygon {m : ℕ} [NeZero m] (v : Fin m → ℝ × ℝ) (hv : Nondeg v)
    (harea : area v = 1) : Sides m where
  h := hsup v
  u := nrm v
  a := aEnd v
  b := bEnd v
  hab i := by have := len_pos v hv i; rw [len_eq_b_sub_a v hv] at this; linarith
  sum_u1 := by simp_rw [← len_eq_b_sub_a v hv]; exact (sum_len_nrm v hv).1
  sum_u2 := by simp_rw [← len_eq_b_sub_a v hv]; exact (sum_len_nrm v hv).2
  sum_h := by simp_rw [← len_eq_b_sub_a v hv]; rw [sum_len_hsup v hv, harea]; norm_num
  sum_sq := by
    have : ∀ i, bEnd v i ^ 2 - aEnd v i ^ 2 = len v i * (aEnd v i + bEnd v i) := fun i => by
      rw [len_eq_b_sub_a v hv]; ring
    simp_rw [this, len_mul_a_add_b v hv]
    exact sum_shift_sub fun i => dot (v i) (v i)

end Enclosing
