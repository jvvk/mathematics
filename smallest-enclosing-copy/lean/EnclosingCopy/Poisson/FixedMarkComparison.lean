import EnclosingCopy.Poisson.WindowMeasurability
import EnclosingCopy.Poisson.ConditionalWindow

/-!
# Uniform event comparison for iid rare windows with exact fixed marks

The error bound is the sum of count-mass differences and is independent of the
configuration event. Thus events may vary arbitrarily with the sample size.
-/
namespace PoissonPP
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

/-- Mixing the same mark law against different count laws costs at most their
sum of absolute mass differences, uniformly over every measurable event. -/
lemma countMix_event_error (ρ σ : Measure ℕ) [IsProbabilityMeasure ρ]
    [IsProbabilityMeasure σ] (ν : Measure β) [IsProbabilityMeasure ν]
    {A : Set (Sample β)} (hA : MeasurableSet A) :
    |(countMix ρ ν).real A - (countMix σ ν).real A| ≤
      ∑' k : ℕ, |ρ.real {k} - σ.real {k}| := by
  let p := fun k : ℕ => (Measure.pi fun _ : Fin k => ν).real
    ((fun x : Fin k → β => (⟨k, x⟩ : Sample β)) ⁻¹' A)
  have hp (k : ℕ) : |p k| ≤ 1 := by
    rw [abs_of_nonneg measureReal_nonneg]; exact measureReal_le_one
  have hw := hasSum_mass ρ
  have hv := hasSum_mass σ
  have hsw : Summable (fun k => ρ.real {k} * p k) :=
    hw.summable.of_norm_bounded fun k => by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg measureReal_nonneg]
      simpa only [mul_one] using mul_le_mul_of_nonneg_left (hp k) measureReal_nonneg
  have hsv : Summable (fun k => σ.real {k} * p k) :=
    hv.summable.of_norm_bounded fun k => by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg measureReal_nonneg]
      simpa only [mul_one] using mul_le_mul_of_nonneg_left (hp k) measureReal_nonneg
  have hsd := (hw.summable.sub hv.summable).abs
  rw [countMix_real _ _ hA, countMix_real _ _ hA]
  change |(∑' k, ρ.real {k} * p k) - ∑' k, σ.real {k} * p k| ≤ _
  rw [← hsw.tsum_sub hsv, ← Real.norm_eq_abs]
  refine (norm_tsum_le_tsum_norm (hsw.sub hsv).norm).trans ?_
  apply Summable.tsum_le_tsum _ (hsw.sub hsv).norm hsd
  intro k
  rw [← sub_mul, Real.norm_eq_abs, abs_mul]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left (hp k) (abs_nonneg _)

/-- Exact marked iid window law, using the canonical conditional distribution. -/
lemma iid_marked_window_prob (μ : Measure α) [IsProbabilityMeasure μ]
    {B : Set α} (hB : MeasurableSet B) (mark : α → β) (hm : Measurable mark)
    (E : Multiset β → Prop)
    (hE : ∀ k, MeasurableSet {x : Fin k → β | E (config x)}) (n : ℕ) :
    (Measure.pi fun _ : Fin n => μ)
      {x | E ((inWindow B (config x)).map mark)} =
      countMix (ProbabilityTheory.binomial n
        ⟨μ.real B, measureReal_nonneg, measureReal_le_one⟩)
        (Measure.map mark (windowLaw μ B)) {ω | E (config ω.2)} := by
  let p : unitInterval := ⟨μ.real B, measureReal_nonneg, measureReal_le_one⟩
  have hp : ENNReal.ofReal (p : ℝ) = μ B := ENNReal.ofReal_toReal (measure_ne_top _ _)
  have hraw k : MeasurableSet {x : Fin k → α | E ((config x).map mark)} := by
    have hf : Measurable (fun x : Fin k → α => mark ∘ x) :=
      measurable_pi_iff.mpr fun i => hm.comp (measurable_pi_apply i)
    simpa [config_map, Function.comp_def] using (hE k).preimage hf
  have hEB k : MeasurableSet {x : Fin k → α | E ((inWindow B (config x)).map mark)} :=
    measurableSet_window_event hB mark hm E hE
  rw [iid_window_prob μ (windowLaw μ B) hB p
    (by rw [hp]; exact windowLaw_restrict μ B)
    (fun c => E (c.map mark)) hraw hEB n]
  rw [countMix_apply _ _ (measurableSet_sample (fun k => by exact hraw k)),
    countMix_apply _ _ (measurableSet_sample (fun k => by exact hE k))]
  congr 1; funext k
  congr 1
  exact tuple_map_event (windowLaw μ B) mark hm E hE k

/-- Event-independent error bound whenever the conditional marks are exactly fixed. -/
theorem iid_fixed_mark_event_error (μ : Measure α) [IsProbabilityMeasure μ]
    {B : Set α} (hB : MeasurableSet B) (mark : α → β) (hm : Measurable mark)
    (ν : Measure β) [IsProbabilityMeasure ν]
    (hfixed : Measure.map mark (windowLaw μ B) = ν) (r : ℝ≥0)
    (E : Multiset β → Prop)
    (hE : ∀ k, MeasurableSet {x : Fin k → β | E (config x)}) (n : ℕ) :
    |(Measure.pi fun _ : Fin n => μ).real {x | E ((inWindow B (config x)).map mark)} -
      (law ((r : ℝ≥0∞) • ν)).real {ω | E (config ω.2)}| ≤
      ∑' k : ℕ, |(ProbabilityTheory.binomial n
        ⟨μ.real B, measureReal_nonneg, measureReal_le_one⟩).real {k} -
          (ProbabilityTheory.poissonMeasure r).real {k}| := by
  rw [measureReal_def, iid_marked_window_prob μ hB mark hm E hE n, hfixed,
    ← countMix_poisson ν r]
  exact countMix_event_error _ _ ν (measurableSet_sample hE)

/-- Uniform convergence over all measurable configuration events, with no event
stability hypothesis, for a rare window having an eventually exact mark law. -/
theorem iid_fixed_mark_uniform_error (μ : ℕ → Measure α)
    [∀ n, IsProbabilityMeasure (μ n)] (B : ℕ → Set α)
    (hB : ∀ n, MeasurableSet (B n)) (mark : ℕ → α → β)
    (hm : ∀ n, Measurable (mark n)) (ν : Measure β) [IsProbabilityMeasure ν]
    {r : ℝ≥0} (hr : Tendsto (fun n : ℕ => (n : ℝ) * (μ n).real (B n))
      atTop (𝓝 (r : ℝ)))
    (hfixed : ∀ᶠ n in atTop, Measure.map (mark n) (windowLaw (μ n) (B n)) = ν) :
    ∀ ε > 0, ∀ᶠ n in atTop, ∀ E : Multiset β → Prop,
      (∀ k, MeasurableSet {x : Fin k → β | E (config x)}) →
      |(Measure.pi fun _ : Fin n => μ n).real
        {x | E ((inWindow (B n) (config x)).map (mark n))} -
        (law ((r : ℝ≥0∞) • ν)).real {ω | E (config ω.2)}| < ε := by
  intro ε hε
  let p : ℕ → unitInterval := fun n =>
    ⟨(μ n).real (B n), measureReal_nonneg, measureReal_le_one⟩
  have hlim := binomial_mass_l1 (p := p) hr
  filter_upwards [hfixed, hlim.eventually (Iio_mem_nhds hε)] with n hn herr E hE
  exact (iid_fixed_mark_event_error (μ n) (hB n) (mark n) (hm n) ν hn r E hE n).trans_lt herr

end PoissonPP
