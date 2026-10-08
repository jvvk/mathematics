import EnclosingCopy.Poisson.Superpose
import EnclosingCopy.Poisson.EventComparison

/-!
# Event probabilities under nearby Poisson intensities

Adding an independent process can change any measurable configuration event only
when the added process is nonempty. The resulting bound depends solely on its
total intensity and imposes no continuity requirement on the event.
-/
namespace PoissonPP
open MeasureTheory Set ENNReal
variable {α : Type*} [MeasurableSpace α]
variable (Λ Ξ : Measure α) [IsFiniteMeasure Λ] [IsFiniteMeasure Ξ]

lemma superpose_event_lower (F : Multiset α → Prop)
    (hF : ∀ k, MeasurableSet {x : Fin k → α | F (config x)}) :
    law Λ {ω | F (config ω.2)} * ENNReal.ofReal (Real.exp (-(Ξ univ).toReal)) ≤
      law (Λ + Ξ) {ω | F (config ω.2)} := by
  classical
  have hs : MeasurableSet {ω : Sample α | F (config ω.2)} := measurableSet_sample hF
  let G : Multiset α → ℝ≥0∞ := fun c => if F c then 1 else 0
  have hG : ConfMeas G := fun k => by
    exact (measurable_one.indicator (hF k))
  have hvoid : MeasurableSet (voidEvent (univ : Set α)) :=
    measurableSet_sample (measurable_void_tuple MeasurableSet.univ)
  have hemp : ∀ ω ∈ voidEvent (univ : Set α), config ω.2 = 0 := by
    intro ω hω
    apply Multiset.eq_zero_iff_forall_notMem.mpr
    intro p hp
    exact hω p hp (mem_univ p)
  have hinner (ω₁ : Sample α) :
      G (config ω₁.2) * law Ξ (voidEvent univ) ≤
        ∫⁻ ω₂, G (config ω₁.2 + config ω₂.2) ∂law Ξ := by
    rw [← lintegral_indicator_const hvoid]
    apply lintegral_mono
    intro ω₂
    by_cases hω₂ : ω₂ ∈ voidEvent (univ : Set α)
    · simp only [indicator_of_mem hω₂, hemp ω₂ hω₂, add_zero]; exact le_rfl
    · simp only [indicator_of_notMem hω₂]; exact zero_le
  have hlower := lintegral_mono (μ := law Λ) hinner
  have hms : Measurable fun ω : Sample α => G (config ω.2) := by
    have hmi : Measurable ({ω : Sample α | F (config ω.2)}.indicator
      (1 : Sample α → ℝ≥0∞)) := measurable_one.indicator hs
    convert hmi using 1
    funext ω
    simp [G, indicator]
  rw [lintegral_mul_const _ hms, superpose Λ Ξ hG] at hlower
  have hprob : (∫⁻ ω, G (config ω.2) ∂law Λ) = law Λ {ω | F (config ω.2)} := by
    simpa only [G, indicator, Pi.one_apply, mem_ofPred_eq] using lintegral_indicator_one hs
  rw [hprob] at hlower
  change law Λ {ω | F (config ω.2)} * law Ξ {ω | ∀ p ∈ config ω.2, p ∉ univ} ≤
    prob (Λ + Ξ) F at hlower
  rw [law_void Ξ MeasurableSet.univ, ← law_prob (Λ + Ξ) F hF] at hlower
  exact hlower

/-- The probability error is bounded by the probability that the added process is nonempty. -/
theorem poisson_add_event_diff_le (F : Multiset α → Prop)
    (hF : ∀ k, MeasurableSet {x : Fin k → α | F (config x)}) :
    |(law (Λ + Ξ)).real {ω | F (config ω.2)} - (law Λ).real {ω | F (config ω.2)}| ≤
      1 - Real.exp (-(Ξ univ).toReal) := by
  have hlow := ENNReal.toReal_mono (measure_ne_top _ _) (superpose_event_lower Λ Ξ F hF)
  have hcomp := ENNReal.toReal_mono (measure_ne_top _ _)
    (superpose_event_lower Λ Ξ (fun c => ¬ F c) (fun k => (hF k).compl))
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.exp_pos _).le] at hlow hcomp
  have he : {ω : Sample α | ¬ F (config ω.2)} = {ω | F (config ω.2)}ᶜ := rfl
  have hs : MeasurableSet {ω : Sample α | F (config ω.2)} := measurableSet_sample hF
  change (law Λ).real {ω | ¬ F (config ω.2)} * Real.exp (-(Ξ univ).toReal) ≤
    (law (Λ + Ξ)).real {ω | ¬ F (config ω.2)} at hcomp
  rw [he, measureReal_compl hs, measureReal_compl hs] at hcomp
  simp only [probReal_univ] at hcomp
  have hq : 0 ≤ Real.exp (-(Ξ univ).toReal) := (Real.exp_pos _).le
  have hq1 : Real.exp (-(Ξ univ).toReal) ≤ 1 :=
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr ENNReal.toReal_nonneg)
  have hp : 0 ≤ (law Λ).real {ω | F (config ω.2)} := measureReal_nonneg
  have hp1 : (law Λ).real {ω | F (config ω.2)} ≤ 1 := measureReal_le_one
  have hprod := mul_nonneg (sub_nonneg.mpr hp1) (sub_nonneg.mpr hq1)
  have hprod' := mul_nonneg hp (sub_nonneg.mpr hq1)
  change (law Λ).real {ω | F (config ω.2)} * Real.exp (-(Ξ univ).toReal) ≤
    (law (Λ + Ξ)).real {ω | F (config ω.2)} at hlow
  exact abs_le.mpr ⟨by nlinarith, by nlinarith⟩

/-- The added intensity itself is an upper bound on every measurable event error. -/
theorem poisson_add_event_diff_le_mass (F : Multiset α → Prop)
    (hF : ∀ k, MeasurableSet {x : Fin k → α | F (config x)}) :
    |(law (Λ + Ξ)).real {ω | F (config ω.2)} - (law Λ).real {ω | F (config ω.2)}| ≤
      Ξ.real univ := by
  apply (poisson_add_event_diff_le Λ Ξ F hF).trans
  have he := Real.add_one_le_exp (-(Ξ univ).toReal)
  change _ ≤ (Ξ univ).toReal
  linarith

end PoissonPP
