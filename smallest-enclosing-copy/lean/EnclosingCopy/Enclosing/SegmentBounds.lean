import EnclosingCopy.Enclosing.SegmentModel
import EnclosingCopy.Enclosing.SegmentProb
import Mathlib.Data.Finset.Lattice.Fold

/-!
# Actual segment endpoints and the fixed-chord probability

`segmentLower` and `segmentUpper` are functions of the sampled Poisson points,
not abstract random variables with assumed laws. Their harmless exterior
floor/ceiling make them real-valued even when a side group contains no points;
on the chord their inequalities are exactly the required void events.

Measurability with respect to the disjoint side-group observations proves their
independence. `chord_feasible_prob` then includes the zero-slope constraints and
proves the full formula `exp(2ε) * (1 + S * chord length)` for any fixed fitting
chord below the depth cutoff. Counting the random optimal chords by three-point
Mecke and removing the cutoff are done in `SegmentCount`.
-/

namespace Enclosing
open MeasureTheory Set ENNReal
open scoped Classical
variable {m : ℕ} (K : Sides m)

lemma gx_chord (z : Copy) (t : ℝ × ℝ) (y : ℝ) (p : Pt m) :
    gx K (chordCopy z t y) p = gx K z p + y * dot (K.u p.1) t := by
  simp only [gx, chordCopy, Hs, dot]
  ring

noncomputable def lowerPoint (z : Copy) (t : ℝ × ℝ) (floor : ℝ) (p : Pt m) : ℝ :=
  if 0 < dot (K.u p.1) t then max floor (-gx K z p / dot (K.u p.1) t) else floor

noncomputable def upperPoint (z : Copy) (t : ℝ × ℝ) (ceiling : ℝ) (p : Pt m) : ℝ :=
  if dot (K.u p.1) t < 0 then min ceiling (-gx K z p / dot (K.u p.1) t) else ceiling

/-- A real lower endpoint, using a harmless floor below the chord for empty samples. -/
noncomputable def segmentLower (z : Copy) (t : ℝ × ℝ) (floor : ℝ)
    (ω : PoissonPP.Sample (Pt m)) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty
    (Fin.lastCases floor (fun r : Fin ω.1 => lowerPoint K z t floor (ω.2 r)))

/-- A real upper endpoint, using a harmless ceiling above the chord for empty samples. -/
noncomputable def segmentUpper (z : Copy) (t : ℝ × ℝ) (ceiling : ℝ)
    (ω : PoissonPP.Sample (Pt m)) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty
    (Fin.lastCases ceiling (fun r : Fin ω.1 => upperPoint K z t ceiling (ω.2 r)))

lemma floor_le_segmentLower (z : Copy) (t : ℝ × ℝ) (floor : ℝ)
    (ω : PoissonPP.Sample (Pt m)) : floor ≤ segmentLower K z t floor ω := by
  unfold segmentLower
  have h := Finset.le_sup' (s := Finset.univ) (Fin.lastCases floor
    (fun r : Fin ω.1 => lowerPoint K z t floor (ω.2 r))) (Finset.mem_univ (Fin.last ω.1))
  simpa only [Fin.lastCases_last] using h

lemma segmentUpper_le_ceiling (z : Copy) (t : ℝ × ℝ) (ceiling : ℝ)
    (ω : PoissonPP.Sample (Pt m)) : segmentUpper K z t ceiling ω ≤ ceiling := by
  unfold segmentUpper
  have h := Finset.inf'_le (s := Finset.univ) (Fin.lastCases ceiling
    (fun r : Fin ω.1 => upperPoint K z t ceiling (ω.2 r))) (Finset.mem_univ (Fin.last ω.1))
  simpa only [Fin.lastCases_last] using h

lemma segmentLower_le_iff (z : Copy) (t : ℝ × ℝ) (floor y : ℝ)
    (hy : floor ≤ y) (ω : PoissonPP.Sample (Pt m)) :
    segmentLower K z t floor ω ≤ y ↔
      ω ∈ PoissonPP.voidEvent (maskedVz K (positiveSides K t) (chordCopy z t y)) := by
  have hpoint : ∀ p : Pt m, lowerPoint K z t floor p ≤ y ↔
      (0 < dot (K.u p.1) t → 0 ≤ gx K (chordCopy z t y) p) := by
    intro p
    by_cases hp : 0 < dot (K.u p.1) t
    · rw [lowerPoint, ite_eq_left hp, max_le_iff]
      simp only [hy, true_and, hp, true_implies, gx_chord]
      rw [div_le_iff₀ hp]
      constructor <;> intro h <;> linarith
    · simp [lowerPoint, hp, hy]
  have hv : ω ∈ PoissonPP.voidEvent (maskedVz K (positiveSides K t) (chordCopy z t y)) ↔
      ∀ r, lowerPoint K z t floor (ω.2 r) ≤ y := by
    simp only [PoissonPP.voidEvent, mem_ofPred_eq, PoissonPP.mem_config]
    constructor
    · intro h r
      rw [hpoint]
      intro hp
      apply (gx_nonneg_iff K _ _).mpr
      intro hviol
      apply h (ω.2 r) ⟨r, rfl⟩
      exact ⟨by simpa [sideRegion, positiveSides] using hp, hviol⟩
    · intro h p hr hp
      obtain ⟨r, hr⟩ := hr
      rw [← hr] at hp
      have hpos : 0 < dot (K.u (ω.2 r).1) t := by
        simpa [sideRegion, positiveSides] using hp.1
      exact (gx_nonneg_iff K _ _).mp ((hpoint _).mp (h r) hpos) hp.2
  rw [hv]
  simp only [segmentLower, Finset.sup'_le_iff, Finset.mem_univ, true_implies]
  constructor
  · intro h r
    simpa only [Fin.lastCases_castSucc] using h r.castSucc
  · intro h r
    cases r using Fin.lastCases
    · simpa only [Fin.lastCases_last] using hy
    · simpa only [Fin.lastCases_castSucc] using h _

lemma le_segmentUpper_iff (z : Copy) (t : ℝ × ℝ) (ceiling y : ℝ)
    (hy : y ≤ ceiling) (ω : PoissonPP.Sample (Pt m)) :
    y ≤ segmentUpper K z t ceiling ω ↔
      ω ∈ PoissonPP.voidEvent (maskedVz K (negativeSides K t) (chordCopy z t y)) := by
  have hpoint : ∀ p : Pt m, y ≤ upperPoint K z t ceiling p ↔
      (dot (K.u p.1) t < 0 → 0 ≤ gx K (chordCopy z t y) p) := by
    intro p
    by_cases hp : dot (K.u p.1) t < 0
    · rw [upperPoint, ite_eq_left hp, le_min_iff]
      simp only [hy, true_and, hp, true_implies, gx_chord]
      rw [le_div_iff_of_neg hp]
      constructor <;> intro h <;> linarith
    · simp [upperPoint, hp, hy]
  have hv : ω ∈ PoissonPP.voidEvent (maskedVz K (negativeSides K t) (chordCopy z t y)) ↔
      ∀ r, y ≤ upperPoint K z t ceiling (ω.2 r) := by
    simp only [PoissonPP.voidEvent, mem_ofPred_eq, PoissonPP.mem_config]
    constructor
    · intro h r
      rw [hpoint]
      intro hp
      apply (gx_nonneg_iff K _ _).mpr
      intro hviol
      apply h (ω.2 r) ⟨r, rfl⟩
      exact ⟨by simpa [sideRegion, negativeSides] using hp, hviol⟩
    · intro h p hr hp
      obtain ⟨r, hr⟩ := hr
      rw [← hr] at hp
      have hneg : dot (K.u (ω.2 r).1) t < 0 := by
        simpa [sideRegion, negativeSides] using hp.1
      exact (gx_nonneg_iff K _ _).mp ((hpoint _).mp (h r) hneg) hp.2
  rw [hv]
  simp only [segmentUpper, Finset.le_inf'_iff, Finset.mem_univ, true_implies]
  constructor
  · intro h r
    simpa only [Fin.lastCases_castSucc] using h r.castSucc
  · intro h r
    cases r using Fin.lastCases
    · simpa only [Fin.lastCases_last] using hy
    · simpa only [Fin.lastCases_castSucc] using h _

lemma segmentLower_void_measurable (z : Copy) (t : ℝ × ℝ) (floor : ℝ) :
    @Measurable _ _
      (MeasurableSpace.generateFrom (PoissonPP.voidFamily (sideRegion (positiveSides K t))))
      _ (segmentLower K z t floor) := by
  let : MeasurableSpace (PoissonPP.Sample (Pt m)) :=
    MeasurableSpace.generateFrom (PoissonPP.voidFamily (sideRegion (positiveSides K t)))
  apply measurable_of_Iic
  intro y
  by_cases hy : floor ≤ y
  · have he : segmentLower K z t floor ⁻¹' Iic y =
        PoissonPP.voidEvent (maskedVz K (positiveSides K t) (chordCopy z t y)) := by
      ext ω; exact segmentLower_le_iff K z t floor y hy ω
    rw [he]
    exact MeasurableSpace.measurableSet_generateFrom
      ⟨_, inter_subset_left, measurableSet_maskedVz K _ _, rfl⟩
  · have he : segmentLower K z t floor ⁻¹' Iic y = ∅ := by
      ext ω
      simp only [mem_preimage, mem_Iic, mem_empty_iff_false, iff_false]
      exact fun h => hy ((floor_le_segmentLower K z t floor ω).trans h)
    rw [he]; exact MeasurableSet.empty

lemma segmentUpper_void_measurable (z : Copy) (t : ℝ × ℝ) (ceiling : ℝ) :
    @Measurable _ _
      (MeasurableSpace.generateFrom (PoissonPP.voidFamily (sideRegion (negativeSides K t))))
      _ (segmentUpper K z t ceiling) := by
  let : MeasurableSpace (PoissonPP.Sample (Pt m)) :=
    MeasurableSpace.generateFrom (PoissonPP.voidFamily (sideRegion (negativeSides K t)))
  apply measurable_of_Ici
  intro y
  by_cases hy : y ≤ ceiling
  · have he : segmentUpper K z t ceiling ⁻¹' Ici y =
        PoissonPP.voidEvent (maskedVz K (negativeSides K t) (chordCopy z t y)) := by
      ext ω; exact le_segmentUpper_iff K z t ceiling y hy ω
    rw [he]
    exact MeasurableSpace.measurableSet_generateFrom
      ⟨_, inter_subset_left, measurableSet_maskedVz K _ _, rfl⟩
  · have he : segmentUpper K z t ceiling ⁻¹' Ici y = ∅ := by
      ext ω
      simp only [mem_preimage, mem_Ici, mem_empty_iff_false, iff_false]
      exact fun h => hy (h.trans (segmentUpper_le_ceiling K z t ceiling ω))
    rw [he]; exact MeasurableSet.empty

lemma measurable_segmentLower (z : Copy) (t : ℝ × ℝ) (floor : ℝ) :
    Measurable (segmentLower K z t floor) :=
  (segmentLower_void_measurable K z t floor).mono
    (MeasurableSpace.generateFrom_le (PoissonPP.voidFamily_measurable _)) le_rfl

lemma measurable_segmentUpper (z : Copy) (t : ℝ × ℝ) (ceiling : ℝ) :
    Measurable (segmentUpper K z t ceiling) :=
  (segmentUpper_void_measurable K z t ceiling).mono
    (MeasurableSpace.generateFrom_le (PoissonPP.voidFamily_measurable _)) le_rfl

/-- Independence of the actual endpoint random variables, derived from void events. -/
theorem segment_bounds_independent (T : ℝ) (z : Copy) (t : ℝ × ℝ) (floor ceiling : ℝ) :
    ProbabilityTheory.IndepFun (segmentLower K z t floor) (segmentUpper K z t ceiling)
      (PoissonPP.law (Λ K T)) := by
  apply PoissonPP.indep_of_void_measurable (Λ K T) _
    (segmentLower K z t floor) (segmentUpper K z t ceiling)
    (segmentLower_void_measurable K z t floor) (segmentUpper_void_measurable K z t ceiling)
  rw [Set.disjoint_left]
  intro x hx hy
  have hp : 0 < dot (K.u x.1) t := by simpa [sideRegion, positiveSides] using hx
  have hn : dot (K.u x.1) t < 0 := by simpa [sideRegion, negativeSides] using hy
  linarith

theorem segmentLower_cdf (T : ℝ) (z : Copy) (t : ℝ × ℝ) (floor y : ℝ) (hy : floor ≤ y)
    (hE : Fits K (chordCopy z t y)) (hT : Below K T (chordCopy z t y)) :
    (PoissonPP.law (Λ K T)).real {ω | segmentLower K z t floor ω ≤ y} =
      maskVoidFn K (positiveSides K t) z t y := by
  have he : {ω | segmentLower K z t floor ω ≤ y} =
      PoissonPP.voidEvent (maskedVz K (positiveSides K t) (chordCopy z t y)) := by
    ext ω; exact segmentLower_le_iff K z t floor y hy ω
  rw [measureReal_def, he, model_void_mask K _ T _ hE hT, ENNReal.toReal_ofReal]
  · rfl
  · exact (Real.exp_pos _).le

theorem segmentUpper_survival (T : ℝ) (z : Copy) (t : ℝ × ℝ) (ceiling y : ℝ)
    (hy : y ≤ ceiling) (hE : Fits K (chordCopy z t y)) (hT : Below K T (chordCopy z t y)) :
    (PoissonPP.law (Λ K T)).real {ω | y ≤ segmentUpper K z t ceiling ω} =
      maskVoidFn K (negativeSides K t) z t y := by
  have he : {ω | y ≤ segmentUpper K z t ceiling ω} =
      PoissonPP.voidEvent (maskedVz K (negativeSides K t) (chordCopy z t y)) := by
    ext ω; exact le_segmentUpper_iff K z t ceiling y hy ω
  rw [measureReal_def, he, model_void_mask K _ T _ hE hT, ENNReal.toReal_ofReal]
  · rfl
  · exact (Real.exp_pos _).le

lemma tangent_balance (t : ℝ × ℝ) : ∑ i, (K.b i - K.a i) * dot (K.u i) t = 0 := by
  simp only [dot, mul_add, Finset.sum_add_distrib]
  have h1 : ∑ i, (K.b i - K.a i) * ((K.u i).1 * t.1) =
      (∑ i, (K.b i - K.a i) * (K.u i).1) * t.1 := by
    rw [Finset.sum_mul]; apply Finset.sum_congr rfl; intro i _; ring
  have h2 : ∑ i, (K.b i - K.a i) * ((K.u i).2 * t.2) =
      (∑ i, (K.b i - K.a i) * (K.u i).2) * t.2 := by
    rw [Finset.sum_mul]; apply Finset.sum_congr rfl; intro i _; ring
  rw [h1, h2, K.sum_u1, K.sum_u2]
  ring

lemma tangent_group_balance (t : ℝ × ℝ) :
    (∑ i ∈ positiveSides K t, (K.b i - K.a i) * dot (K.u i) t) +
      (∑ i ∈ negativeSides K t, (K.b i - K.a i) * dot (K.u i) t) = 0 := by
  rw [← tangent_balance K t]
  simp only [positiveSides, negativeSides, Finset.sum_filter]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rcases lt_trichotomy (dot (K.u i) t) 0 with hn | hz | hp
  · simp [hn, not_lt_of_ge hn.le]
  · simp [hz]
  · simp [hp, not_lt_of_ge hp.le]

lemma tangent_positiveSlope_nonneg (t : ℝ × ℝ) :
    0 ≤ ∑ i ∈ positiveSides K t, (K.b i - K.a i) * dot (K.u i) t := by
  apply Finset.sum_nonneg
  intro i hi
  exact mul_nonneg (sub_nonneg.mpr (K.hab i).le) (Finset.mem_filter.mp hi).2.le

lemma segment_mask_product (z : Copy) (t : ℝ × ℝ) (y : ℝ) :
    maskVoidFn K (positiveSides K t) z t y * maskVoidFn K (negativeSides K t) z t y =
      Real.exp (-maskedVoidArea K (positiveSides K t) z -
        maskedVoidArea K (negativeSides K t) z) := by
  unfold maskVoidFn
  rw [← Real.exp_add, maskedVoidArea_chord, maskedVoidArea_chord]
  have h := tangent_group_balance K t
  congr 1
  linear_combination y * h

lemma continuous_maskVoidFn (J : Finset (Fin m)) (z : Copy) (t : ℝ × ℝ) :
    Continuous (maskVoidFn K J z t) :=
  continuous_iff_continuousAt.mpr fun y => (maskVoidFn_deriv K J z t y).continuousAt

/-- The segment/chord probability formula applied to the actual Poisson endpoint variables.
The constraints on sides perpendicular to `t` are separate; this theorem treats exactly
the lower- and upper-bound groups. -/
theorem segment_bounds_event_prob (T : ℝ) (z : Copy) (t : ℝ × ℝ) (α β : ℝ)
    (hαβ : α ≤ β) (hE : ∀ y ∈ Icc α β, Fits K (chordCopy z t y))
    (hT : ∀ y ∈ Icc α β, Below K T (chordCopy z t y)) :
    (PoissonPP.law (Λ K T)).real
      {ω | segmentLower K z t (α - 1) ω ≤ β ∧
        α ≤ segmentUpper K z t (β + 1) ω ∧
        segmentLower K z t (α - 1) ω ≤ segmentUpper K z t (β + 1) ω} =
      Real.exp (-maskedVoidArea K (positiveSides K t) z -
        maskedVoidArea K (negativeSides K t) z) *
      (1 + (∑ i ∈ positiveSides K t, (K.b i - K.a i) * dot (K.u i) t) * (β - α)) := by
  let F := maskVoidFn K (positiveSides K t) z t
  let G := maskVoidFn K (negativeSides K t) z t
  let S := ∑ i ∈ positiveSides K t, (K.b i - K.a i) * dot (K.u i) t
  have hFc : Continuous F := continuous_maskVoidFn K _ z t
  exact segment_event_closed
    (measurable_segmentLower K z t (α - 1))
    (measurable_segmentUpper K z t (β + 1))
    (segment_bounds_independent K T z t _ _) hαβ
    (fun y hy => segmentLower_cdf K T z t _ y (by linarith [hy.1]) (hE y hy) (hT y hy))
    (fun y hy => segmentUpper_survival K T z t _ y (by linarith [hy.2]) (hE y hy) (hT y hy))
    hFc.continuousOn
    (fun y _ => maskVoidFn_deriv K _ z t y)
    (continuous_const.mul hFc)
    (fun y _ => mul_nonneg (tangent_positiveSlope_nonneg K t) (Real.exp_pos _).le)
    (fun y _ => segment_mask_product K z t y) (fun _ _ => rfl)

lemma segment_bounds_event_iff (z : Copy) (t : ℝ × ℝ) (α β : ℝ) (hαβ : α ≤ β)
    (ω : PoissonPP.Sample (Pt m)) :
    (segmentLower K z t (α - 1) ω ≤ β ∧ α ≤ segmentUpper K z t (β + 1) ω ∧
      segmentLower K z t (α - 1) ω ≤ segmentUpper K z t (β + 1) ω) ↔
    ∃ y ∈ Icc α β,
      ω ∈ PoissonPP.voidEvent (maskedVz K (positiveSides K t) (chordCopy z t y)) ∧
      ω ∈ PoissonPP.voidEvent (maskedVz K (negativeSides K t) (chordCopy z t y)) := by
  constructor
  · rintro ⟨h1, h2, h3⟩
    let y := max α (segmentLower K z t (α - 1) ω)
    have hy : y ∈ Icc α β := ⟨le_max_left _ _, max_le hαβ h1⟩
    refine ⟨y, hy, ?_, ?_⟩
    · exact (segmentLower_le_iff K z t _ y (by linarith [hy.1]) ω).mp (le_max_right _ _)
    · exact (le_segmentUpper_iff K z t _ y (by linarith [hy.2]) ω).mp (max_le h2 h3)
  · rintro ⟨y, hy, hL, hU⟩
    have hL' := (segmentLower_le_iff K z t (α - 1) y (by linarith [hy.1]) ω).mpr hL
    have hU' := (le_segmentUpper_iff K z t (β + 1) y (by linarith [hy.2]) ω).mpr hU
    exact ⟨hL'.trans hy.2, hy.1.trans hU', hL'.trans hU'⟩

noncomputable def zeroSides (t : ℝ × ℝ) : Finset (Fin m) :=
  Finset.univ.filter fun i => dot (K.u i) t = 0

lemma zero_mask_area_chord (z : Copy) (t : ℝ × ℝ) (y : ℝ) :
    maskedVoidArea K (zeroSides K t) (chordCopy z t y) = maskedVoidArea K (zeroSides K t) z := by
  rw [maskedVoidArea_chord]
  have hzero : (∑ i ∈ zeroSides K t, (K.b i - K.a i) * dot (K.u i) t) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    have h : dot (K.u i) t = 0 := (Finset.mem_filter.mp hi).2
    rw [h, mul_zero]
  rw [hzero, zero_mul, sub_zero]

lemma void_observation_mono {J L : Finset (Fin m)} (hJL : J ⊆ L) :
    MeasurableSpace.generateFrom (PoissonPP.voidFamily (sideRegion J)) ≤
      MeasurableSpace.generateFrom (PoissonPP.voidFamily (sideRegion L)) := by
  apply MeasurableSpace.generateFrom_mono
  rintro E ⟨D, hD, hm, rfl⟩
  exact ⟨D, hD.trans (fun _ hx => hJL hx), hm, rfl⟩

lemma three_group_area_sum (z : Copy) (t : ℝ × ℝ) :
    maskedVoidArea K (positiveSides K t) z + maskedVoidArea K (negativeSides K t) z +
      maskedVoidArea K (zeroSides K t) z = -(2 * z.1) := by
  rw [← sum_line_area K z]
  simp only [maskedVoidArea, positiveSides, negativeSides, zeroSides, Finset.sum_filter]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rcases lt_trichotomy (dot (K.u i) t) 0 with hn | hz | hp
  · simp [hn, not_lt_of_ge hn.le, hn.ne, sideVoidArea]
  · simp [hz, sideVoidArea]
  · simp [hp, not_lt_of_ge hp.le, hp.ne', sideVoidArea]

lemma chord_feasible_iff (z : Copy) (t : ℝ × ℝ) (α β : ℝ) (hαβ : α ≤ β)
    (ω : PoissonPP.Sample (Pt m)) :
    (∃ y ∈ Icc α β, Feasible K (PoissonPP.config ω.2) (chordCopy z t y)) ↔
      (segmentLower K z t (α - 1) ω ≤ β ∧ α ≤ segmentUpper K z t (β + 1) ω ∧
        segmentLower K z t (α - 1) ω ≤ segmentUpper K z t (β + 1) ω) ∧
      ω ∈ PoissonPP.voidEvent (maskedVz K (zeroSides K t) z) := by
  have hz : ∀ y, ω ∈ PoissonPP.voidEvent (maskedVz K (zeroSides K t) z) ↔
      ω ∈ PoissonPP.voidEvent (maskedVz K (zeroSides K t) (chordCopy z t y)) := by
    intro y
    have he : maskedVz K (zeroSides K t) z = maskedVz K (zeroSides K t) (chordCopy z t y) := by
      ext p
      change (p.1 ∈ zeroSides K t ∧ violates K z p) ↔
        (p.1 ∈ zeroSides K t ∧ violates K (chordCopy z t y) p)
      by_cases hp : p.1 ∈ zeroSides K t
      · have hdot : dot (K.u p.1) t = 0 := (Finset.mem_filter.mp hp).2
        have hg := gx_chord K z t y p
        simp only [hdot, mul_zero, add_zero] at hg
        simp only [hp, true_and]
        apply not_iff_not.mp
        rw [← gx_nonneg_iff K z p, ← gx_nonneg_iff K (chordCopy z t y) p, hg]
      · simp [hp]
    rw [he]
  rw [segment_bounds_event_iff K z t α β hαβ]
  constructor
  · rintro ⟨y, hy, hf⟩
    have hm : ∀ J, ω ∈ PoissonPP.voidEvent (maskedVz K J (chordCopy z t y)) := by
      intro J p hp hviol
      exact hf p hp hviol.2
    exact ⟨⟨y, hy, hm _, hm _⟩, (hz y).mpr (hm _)⟩
  · rintro ⟨⟨y, hy, hp, hn⟩, h0⟩
    refine ⟨y, hy, ?_⟩
    intro p hmem hviol
    rcases lt_trichotomy (dot (K.u p.1) t) 0 with hneg | hzero | hpos
    · exact hn p hmem ⟨by simpa [sideRegion, negativeSides] using hneg, hviol⟩
    · exact (hz y).mp h0 p hmem ⟨by simpa [sideRegion, zeroSides] using hzero, hviol⟩
    · exact hp p hmem ⟨by simpa [sideRegion, positiveSides] using hpos, hviol⟩

/-- The full fixed-chord void probability, including the zero-slope constraints. -/
theorem chord_feasible_prob (T : ℝ) (z : Copy) (t : ℝ × ℝ) (α β : ℝ)
    (hαβ : α ≤ β) (hE : ∀ y ∈ Icc α β, Fits K (chordCopy z t y))
    (hT : ∀ y ∈ Icc α β, Below K T (chordCopy z t y)) :
    (PoissonPP.law (Λ K T)).real
      {ω | ∃ y ∈ Icc α β, Feasible K (PoissonPP.config ω.2) (chordCopy z t y)} =
      Real.exp (2 * z.1) *
        (1 + (∑ i ∈ positiveSides K t, (K.b i - K.a i) * dot (K.u i) t) * (β - α)) := by
  let A : Set (PoissonPP.Sample (Pt m)) :=
    {ω | segmentLower K z t (α - 1) ω ≤ β ∧ α ≤ segmentUpper K z t (β + 1) ω ∧
      segmentLower K z t (α - 1) ω ≤ segmentUpper K z t (β + 1) ω}
  let B := PoissonPP.voidEvent (maskedVz K (zeroSides K t) z)
  let J := positiveSides K t ∪ negativeSides K t
  have hA : MeasurableSet[
      MeasurableSpace.generateFrom (PoissonPP.voidFamily (sideRegion J))] A := by
    let : MeasurableSpace (PoissonPP.Sample (Pt m)) :=
      MeasurableSpace.generateFrom (PoissonPP.voidFamily (sideRegion J))
    have hL : Measurable (segmentLower K z t (α - 1)) :=
      (segmentLower_void_measurable K z t (α - 1)).mono
        (void_observation_mono (L := J) Finset.subset_union_left) le_rfl
    have hU : Measurable (segmentUpper K z t (β + 1)) :=
      (segmentUpper_void_measurable K z t (β + 1)).mono
        (void_observation_mono (L := J) Finset.subset_union_right) le_rfl
    exact (measurableSet_le hL measurable_const).inter
      ((measurableSet_le measurable_const hU).inter (measurableSet_le hL hU))
  have hB : MeasurableSet[
      MeasurableSpace.generateFrom (PoissonPP.voidFamily (sideRegion (zeroSides K t)))] B :=
    MeasurableSpace.measurableSet_generateFrom
      ⟨_, inter_subset_left, measurableSet_maskedVz K _ _, rfl⟩
  have hdis : Disjoint (sideRegion J) (sideRegion (zeroSides K t)) := by
    rw [Set.disjoint_left]
    intro p hp h0
    change p.1 ∈ zeroSides K t at h0
    have hz : dot (K.u p.1) t = 0 := (Finset.mem_filter.mp h0).2
    change p.1 ∈ positiveSides K t ∪ negativeSides K t at hp
    rcases Finset.mem_union.mp hp with hp | hn
    · exact (Finset.mem_filter.mp hp).2.ne' hz
    · exact (Finset.mem_filter.mp hn).2.ne hz
  have hi := (ProbabilityTheory.Indep_iff _ _ _).mp
    (PoissonPP.void_sigma_independent (Λ K T) hdis) A B hA hB
  have he : {ω | ∃ y ∈ Icc α β, Feasible K (PoissonPP.config ω.2) (chordCopy z t y)} = A ∩ B := by
    ext ω; exact chord_feasible_iff K z t α β hαβ ω
  have hAB : (PoissonPP.law (Λ K T)).real (A ∩ B) =
      (PoissonPP.law (Λ K T)).real A * (PoissonPP.law (Λ K T)).real B := by
    simp only [measureReal_def, hi, ENNReal.toReal_mul]
  rw [he, hAB, segment_bounds_event_prob K T z t α β hαβ hE hT]
  have hBr : (PoissonPP.law (Λ K T)).real B = Real.exp (-maskedVoidArea K (zeroSides K t) z) := by
    have hzm : maskedVz K (zeroSides K t) z = maskedVz K (zeroSides K t) (chordCopy z t α) := by
      ext p
      change (p.1 ∈ zeroSides K t ∧ violates K z p) ↔
        (p.1 ∈ zeroSides K t ∧ violates K (chordCopy z t α) p)
      by_cases hp : p.1 ∈ zeroSides K t
      · have hdot : dot (K.u p.1) t = 0 := (Finset.mem_filter.mp hp).2
        have hg := gx_chord K z t α p
        simp only [hdot, mul_zero, add_zero] at hg
        simp only [hp, true_and]
        apply not_iff_not.mp
        rw [← gx_nonneg_iff K z p, ← gx_nonneg_iff K (chordCopy z t α) p, hg]
      · simp [hp]
    change (PoissonPP.law (Λ K T)).real
      (PoissonPP.voidEvent (maskedVz K (zeroSides K t) z)) = _
    rw [measureReal_def, hzm, model_void_mask K _ T _ (hE α ⟨le_rfl, hαβ⟩)
      (hT α ⟨le_rfl, hαβ⟩), ENNReal.toReal_ofReal (Real.exp_pos _).le,
      zero_mask_area_chord]
  rw [hBr]
  have hsum := three_group_area_sum K z t
  have hexp : Real.exp (-maskedVoidArea K (positiveSides K t) z -
      maskedVoidArea K (negativeSides K t) z) * Real.exp (-maskedVoidArea K (zeroSides K t) z) =
      Real.exp (2 * z.1) := by
    rw [← Real.exp_add]
    congr 1
    linarith
  calc _ = (Real.exp (-maskedVoidArea K (positiveSides K t) z -
      maskedVoidArea K (negativeSides K t) z) * Real.exp (-maskedVoidArea K (zeroSides K t) z)) *
      (1 + (∑ i ∈ positiveSides K t, (K.b i - K.a i) * dot (K.u i) t) * (β - α)) := by ring
    _ = _ := by rw [hexp]

end Enclosing
