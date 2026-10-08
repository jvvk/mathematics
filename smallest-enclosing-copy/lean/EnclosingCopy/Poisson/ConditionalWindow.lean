import EnclosingCopy.Poisson.WindowLimit
import Mathlib.Probability.ConditionalProbability

/-!
# Canonical conditional laws for iid observation windows

Zero-mass windows use the original sampling law as an irrelevant fallback. Every
window therefore has a probability-valued conditional law, and its restriction
identity holds without positive-mass assumptions. An exact rescaled intensity
identity determines the mapped conditional law.
-/
namespace PoissonPP
open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal
variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

/-- Conditional law in a window, with a probability-valued fallback at mass zero. -/
noncomputable def windowLaw (μ : Measure α) (B : Set α) : Measure α :=
  if μ B = 0 then μ else ProbabilityTheory.cond μ B

instance windowLaw_probability (μ : Measure α) [IsProbabilityMeasure μ] (B : Set α) :
    IsProbabilityMeasure (windowLaw μ B) := by
  classical
  unfold windowLaw
  split_ifs with h
  · infer_instance
  · exact ProbabilityTheory.cond_isProbabilityMeasure h

/-- The canonical conditional law gives the exact restriction identity, even at mass zero. -/
theorem windowLaw_restrict (μ : Measure α) [IsProbabilityMeasure μ] (B : Set α) :
    μ.restrict B = μ B • windowLaw μ B := by
  classical
  by_cases h : μ B = 0
  · simp [windowLaw, h, Measure.restrict_eq_zero.mpr h]
  · rw [windowLaw, ite_eq_right h, ProbabilityTheory.cond, smul_smul,
      ENNReal.mul_inv_cancel h (measure_ne_top μ B), one_smul]

/-- Mapping an unnormalized window to a scaled finite intensity determines its count mass. -/
theorem mapped_window_mass (μ : Measure α) (B : Set α) (f : α → β) (hf : Measurable f)
    (Λ : Measure β) (c : ℝ≥0∞) (hmap : Measure.map f (μ.restrict B) = c • Λ) :
    μ B = c * Λ univ := by
  have he := congrArg (fun ρ : Measure β => ρ univ) hmap
  simpa only [Measure.map_apply hf MeasurableSet.univ, preimage_univ,
    Measure.restrict_apply_univ, Measure.smul_apply, smul_eq_mul] using he

/-- **Exact mapped conditional law from a scaled spatial intensity.** -/
theorem mapped_windowLaw (μ : Measure α) [IsProbabilityMeasure μ] (B : Set α)
    (f : α → β) (hf : Measurable f) (Λ : Measure β) [IsFiniteMeasure Λ]
    (hΛ : Λ univ ≠ 0) (c : ℝ≥0∞) (hc : c ≠ 0) (hct : c ≠ ⊤)
    (hmap : Measure.map f (μ.restrict B) = c • Λ) :
    Measure.map f (windowLaw μ B) = (Λ univ)⁻¹ • Λ := by
  classical
  have hm := mapped_window_mass μ B f hf Λ c hmap
  have hB : μ B ≠ 0 := by rw [hm]; exact mul_ne_zero hc hΛ
  rw [windowLaw, ite_eq_right hB, ProbabilityTheory.cond,
    Measure.map_smul _ hf.aemeasurable, hmap, smul_smul, hm,
    ENNReal.mul_inv (Or.inl hc) (Or.inl hct)]
  have he : c⁻¹ * (Λ univ)⁻¹ * c = (Λ univ)⁻¹ := by
    rw [mul_right_comm, ENNReal.inv_mul_cancel hc hct, one_mul]
  rw [he]

/-- Apply the iid rare-window limit using its canonical conditional law. -/
theorem iid_canonical_window_limit (μ : ℕ → Measure α) [∀ n, IsProbabilityMeasure (μ n)]
    (ν : Measure β) [IsProbabilityMeasure ν] (B : ℕ → Set α)
    (hB : ∀ n, MeasurableSet (B n)) (mark : ℕ → α → β)
    (hmark : ∀ n, Measurable (mark n)) (E : ℕ → Multiset β → Prop) (F : Multiset β → Prop)
    (hE : ∀ n k, MeasurableSet {x : Fin k → β | E n (config x)})
    (hF : ∀ k, MeasurableSet {x : Fin k → β | F (config x)})
    (hEB : ∀ n k, MeasurableSet {x : Fin k → α |
      E n ((inWindow (B n) (config x)).map (mark n))}) {r : ℝ≥0}
    (hr : Tendsto (fun n : ℕ => (n : ℝ) * (μ n).real (B n)) atTop (𝓝 (r : ℝ)))
    (hmarks : ∀ k, Tendsto
      (fun n => (Measure.pi fun _ : Fin k => Measure.map (mark n)
        (windowLaw (μ n) (B n))).real {x | E n (config x)}) atTop
      (𝓝 ((Measure.pi fun _ : Fin k => ν).real {x | F (config x)}))) :
    Tendsto (fun n => (Measure.pi fun _ : Fin n => μ n).real
      {x | E n ((inWindow (B n) (config x)).map (mark n))}) atTop
      (𝓝 ((law ((r : ℝ≥0∞) • ν)).real {ω | F (config ω.2)})) := by
  let p : ℕ → unitInterval := fun n => ⟨(μ n).real (B n), measureReal_nonneg, measureReal_le_one⟩
  have hp n : ENNReal.ofReal (p n : ℝ) = (μ n) (B n) := by
    exact ENNReal.ofReal_toReal (measure_ne_top _ _)
  apply iid_window_event_limit μ (fun n => windowLaw (μ n) (B n)) ν B hB p
    (fun n => by rw [hp n]; exact windowLaw_restrict (μ n) (B n))
    mark hmark E F hE hF hEB hr hmarks

/-- If spatial marks are eventually exactly fixed, only finite-tuple event stability remains. -/
theorem iid_fixed_mark_window_limit (μ : ℕ → Measure α) [∀ n, IsProbabilityMeasure (μ n)]
    (ν : Measure β) [IsProbabilityMeasure ν] (B : ℕ → Set α)
    (hB : ∀ n, MeasurableSet (B n)) (mark : ℕ → α → β)
    (hmark : ∀ n, Measurable (mark n)) (E : ℕ → Multiset β → Prop) (F : Multiset β → Prop)
    (hE : ∀ n k, MeasurableSet {x : Fin k → β | E n (config x)})
    (hF : ∀ k, MeasurableSet {x : Fin k → β | F (config x)})
    (hEB : ∀ n k, MeasurableSet {x : Fin k → α |
      E n ((inWindow (B n) (config x)).map (mark n))}) {r : ℝ≥0}
    (hr : Tendsto (fun n : ℕ => (n : ℝ) * (μ n).real (B n)) atTop (𝓝 (r : ℝ)))
    (hfixed : ∀ᶠ n in atTop, Measure.map (mark n) (windowLaw (μ n) (B n)) = ν)
    (hstable : ∀ k, ∀ᵐ x : Fin k → β ∂(Measure.pi fun _ => ν),
      ∀ᶠ n in atTop, E n (config x) ↔ F (config x)) :
    Tendsto (fun n => (Measure.pi fun _ : Fin n => μ n).real
      {x | E n ((inWindow (B n) (config x)).map (mark n))}) atTop
      (𝓝 ((law ((r : ℝ≥0∞) • ν)).real {ω | F (config ω.2)})) := by
  apply iid_canonical_window_limit μ ν B hB mark hmark E F hE hF hEB hr
  intro k
  have he : (fun n => (Measure.pi fun _ : Fin k => Measure.map (mark n)
      (windowLaw (μ n) (B n))).real {x | E n (config x)}) =ᶠ[atTop]
      (fun n => (Measure.pi fun _ : Fin k => ν).real {x | E n (config x)}) := by
    filter_upwards [hfixed] with n hn
    rw [hn]
  exact (tuple_event_limit_of_ae ν E F hE hF hstable k).congr' he.symm

end PoissonPP
