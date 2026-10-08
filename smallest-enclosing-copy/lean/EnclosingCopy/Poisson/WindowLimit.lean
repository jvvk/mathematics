import EnclosingCopy.Poisson.IIDWindow
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Rare windows of fixed-size iid samples, including coordinate changes

`iid_window_event_limit` is a Poisson limit for actual iid samples restricted to shrinking
windows and mapped to a fixed mark space. It allows the event to vary with sample size.
The required per-count conditional convergence is stated explicitly; establishing it for
the enclosing-copy optimum requires the geometric stability lemma of Theorem 1.
-/
namespace PoissonPP
open MeasureTheory Set ENNReal Filter Topology
open scoped NNReal
variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

omit [MeasurableSpace α] [MeasurableSpace β] in
lemma config_map {k : ℕ} (x : Fin k → α) (f : α → β) :
    (config x).map f = config (f ∘ x) := by
  simp only [config, Multiset.map_map]

/-- Transform the iid conditional marks by a measurable coordinate map. -/
lemma tuple_map_event (ν : Measure α) [IsProbabilityMeasure ν] (f : α → β) (hf : Measurable f)
    (E : Multiset β → Prop)
    (hE : ∀ k, MeasurableSet {x : Fin k → β | E (config x)}) (k : ℕ) :
    (Measure.pi fun _ : Fin k => ν) {x | E ((config x).map f)} =
      (Measure.pi fun _ : Fin k => Measure.map f ν) {x | E (config x)} := by
  have hm : Measurable fun x : Fin k → α => fun i => f (x i) :=
    measurable_pi_iff.mpr fun i => hf.comp (measurable_pi_apply i)
  rw [← Measure.pi_map_pi (fun _ : Fin k => hf.aemeasurable), Measure.map_apply hm (hE k)]
  congr 1
  ext x
  simp [Function.comp_def, config_map]

/-- Conditional events on a fixed mark law converge whenever their indicators stabilize
almost surely on every finite tuple. -/
lemma tuple_event_limit_of_ae (ν : Measure β) [IsProbabilityMeasure ν]
    (E : ℕ → Multiset β → Prop) (F : Multiset β → Prop)
    (hE : ∀ n k, MeasurableSet {x : Fin k → β | E n (config x)})
    (hF : ∀ k, MeasurableSet {x : Fin k → β | F (config x)})
    (hstable : ∀ k, ∀ᵐ x : Fin k → β ∂(Measure.pi fun _ => ν),
      ∀ᶠ n in atTop, E n (config x) ↔ F (config x)) (k : ℕ) :
    Tendsto (fun n => (Measure.pi fun _ : Fin k => ν).real {x | E n (config x)})
      atTop (𝓝 ((Measure.pi fun _ : Fin k => ν).real {x | F (config x)})) := by
  have ht : Tendsto (fun n => (Measure.pi fun _ : Fin k => ν) {x | E n (config x)})
      atTop (𝓝 ((Measure.pi fun _ : Fin k => ν) {x | F (config x)})) := by
    simp_rw [← lintegral_indicator_one (hE _ k), ← lintegral_indicator_one (hF k)]
    refine tendsto_lintegral_of_dominated_convergence (fun _ => 1)
      (fun n => measurable_one.indicator (hE n k))
      (fun n => Eventually.of_forall fun x => by
        by_cases h : E n (config x) <;> simp [indicator, h])
      (by simp) ?_
    filter_upwards [hstable k] with x hx
    have he : (fun n => {x | E n (config x)}.indicator (1 : (Fin k → β) → ℝ≥0∞) x)
        =ᶠ[atTop] (fun _ : ℕ => {x | F (config x)}.indicator (1 : (Fin k → β) → ℝ≥0∞) x) := by
      filter_upwards [hx] with n hn
      by_cases h : F (config x)
      · simp [indicator, h, hn.mpr h]
      · have hn' : ¬ E n (config x) := fun h' => h (hn.mp h')
        simp [indicator, h, hn']
    exact tendsto_const_nhds.congr' he.symm
  exact (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp ht

/-- **Fixed-size iid rare-window Poisson limit**, after a measurable coordinate change.
No Poissonization or de-Poissonization is assumed. Spatial mark convergence and optimum-event
stability are the explicit hypothesis `hmarks`, supplied by the geometry. -/
theorem iid_window_event_limit (μ νn : ℕ → Measure α)
    [∀ n, IsProbabilityMeasure (μ n)] [∀ n, IsProbabilityMeasure (νn n)]
    (ν : Measure β) [IsProbabilityMeasure ν]
    (B : ℕ → Set α) (hB : ∀ n, MeasurableSet (B n)) (p : ℕ → unitInterval)
    (hνn : ∀ n, (μ n).restrict (B n) = ENNReal.ofReal (p n : ℝ) • νn n)
    (mark : ℕ → α → β) (hmark : ∀ n, Measurable (mark n))
    (E : ℕ → Multiset β → Prop) (F : Multiset β → Prop)
    (hE : ∀ n k, MeasurableSet {x : Fin k → β | E n (config x)})
    (hF : ∀ k, MeasurableSet {x : Fin k → β | F (config x)})
    (hEB : ∀ n k, MeasurableSet {x : Fin k → α |
      E n ((inWindow (B n) (config x)).map (mark n))}) {r : ℝ≥0}
    (hr : Tendsto (fun n : ℕ => (n : ℝ) * (p n : ℝ)) atTop (𝓝 (r : ℝ)))
    (hmarks : ∀ k : ℕ, Tendsto
      (fun n => (Measure.pi fun _ : Fin k => Measure.map (mark n) (νn n)).real
        {x | E n (config x)})
      atTop (𝓝 ((Measure.pi fun _ : Fin k => ν).real {x | F (config x)}))) :
    Tendsto (fun n => (Measure.pi fun _ : Fin n => μ n).real
      {x | E n ((inWindow (B n) (config x)).map (mark n))})
      atTop (𝓝 ((law ((r : ℝ≥0∞) • ν)).real {ω | F (config ω.2)})) := by
  have hraw n k : MeasurableSet {x : Fin k → α | E n ((config x).map (mark n))} := by
    have hm : Measurable fun x : Fin k → α => mark n ∘ x :=
      measurable_pi_iff.mpr fun i => (hmark n).comp (measurable_pi_apply i)
    simpa [config_map, Function.comp_def] using (hE n k).preimage hm
  have hmap n : countMix (ProbabilityTheory.binomial n (p n)) (νn n)
      {ω | E n ((config ω.2).map (mark n))} =
        countMix (ProbabilityTheory.binomial n (p n)) (Measure.map (mark n) (νn n))
          {ω | E n (config ω.2)} := by
    rw [countMix_apply _ _ (measurableSet_sample (fun k => by exact hraw n k)),
      countMix_apply _ _ (measurableSet_sample (fun k => by exact hE n k))]
    congr 1; funext k
    congr 1
    exact tuple_map_event (νn n) (mark n) (hmark n) (E n) (hE n) k
  have heq n : (Measure.pi fun _ : Fin n => μ n)
      {x | E n ((inWindow (B n) (config x)).map (mark n))} =
        countMix (ProbabilityTheory.binomial n (p n)) (Measure.map (mark n) (νn n))
          {ω | E n (config ω.2)} :=
    (iid_window_prob (μ n) (νn n) (hB n) (p n) (hνn n)
      (fun c => E n (c.map (mark n))) (hraw n) (hEB n) n).trans (hmap n)
  simp only [measureReal_def, heq]
  exact marked_binomial_event_limit ν (fun n => Measure.map (mark n) (νn n))
    (fun n => measurableSet_sample (fun k => by exact hE n k)) (measurableSet_sample hF) hr hmarks

end PoissonPP
