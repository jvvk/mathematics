import EnclosingCopy.Poisson.WindowLimit

/-! # Probability convergence from almost-sure event stabilization -/
namespace PoissonPP
open MeasureTheory Set Filter Topology
open scoped ENNReal
variable {α : Type*} [MeasurableSpace α]

/-- Event indicators stabilizing almost surely give convergence of their probabilities. -/
lemma event_probability_limit_of_ae (μ : Measure α) [IsProbabilityMeasure μ]
    (E : ℕ → α → Prop) (F : α → Prop)
    (hE : ∀ n, MeasurableSet {x | E n x}) (hF : MeasurableSet {x | F x})
    (hstable : ∀ᵐ x ∂μ, ∀ᶠ n in atTop, E n x ↔ F x) :
    Tendsto (fun n => μ.real {x | E n x}) atTop (𝓝 (μ.real {x | F x})) := by
  have ht : Tendsto (fun n => μ {x | E n x})
      atTop (𝓝 (μ {x | F x})) := by
    simp_rw [← lintegral_indicator_one (hE _), ← lintegral_indicator_one hF]
    refine tendsto_lintegral_of_dominated_convergence (fun _ => 1)
      (fun n => measurable_one.indicator (hE n))
      (fun n => Eventually.of_forall fun x => by
        by_cases h : E n x <;> simp [indicator, h])
      (by simp) ?_
    filter_upwards [hstable] with x hx
    have he : (fun n => {x | E n x}.indicator (1 : α → ℝ≥0∞) x)
        =ᶠ[atTop] (fun _ : ℕ => {x | F x}.indicator (1 : α → ℝ≥0∞) x) := by
      filter_upwards [hx] with n hn
      by_cases h : F x
      · simp [indicator, h, hn.mpr h]
      · have hn' : ¬ E n x := fun h' => h (hn.mp h')
        simp [indicator, h, hn']
    exact tendsto_const_nhds.congr' he.symm
  exact (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp ht


end PoissonPP
