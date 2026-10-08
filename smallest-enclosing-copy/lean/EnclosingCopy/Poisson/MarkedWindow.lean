import EnclosingCopy.Poisson.CountConvergence
import EnclosingCopy.Poisson.Law

/-!
# Fixed-window marked binomial processes converge to the finite Poisson law

`countMix ρ ν` samples a count with law `ρ`, then independent points with law `ν`.
For Poisson counts this agrees exactly with the existing `PoissonPP.law (r • ν)`.
For binomial counts the theorem transfers varying configuration events provided that their
conditional probabilities at every fixed count converge. The spatial/geometric convergence
of the marks and of the optimum event are explicit hypotheses here; the enclosing-polygon
application supplies them in `Enclosing/Theorem1`.
-/
namespace PoissonPP
open MeasureTheory Set ENNReal Filter Topology
open scoped NNReal
variable {α : Type*} [MeasurableSpace α]

/-- A labelled finite sample with prescribed count law and independent mark law. -/
noncomputable def countMix (ρ : Measure ℕ) (ν : Measure α) : Measure (Sample α) :=
  Measure.sum fun k : ℕ => ρ {k} •
    Measure.map (Sigma.mk k) (Measure.pi fun _ : Fin k => ν)

lemma countMix_apply (ρ : Measure ℕ) (ν : Measure α) {A : Set (Sample α)}
    (hA : MeasurableSet A) :
    countMix ρ ν A = ∑' k : ℕ, ρ {k} *
      (Measure.pi fun _ : Fin k => ν) ((fun x : Fin k → α => (⟨k, x⟩ : Sample α)) ⁻¹' A) := by
  rw [countMix, Measure.sum_apply _ hA]
  congr 1; funext k
  rw [Measure.smul_apply, Measure.map_apply (measurable_sampleMk k) hA, smul_eq_mul]

instance (ρ : Measure ℕ) (ν : Measure α) [IsProbabilityMeasure ρ] [IsProbabilityMeasure ν] :
    IsProbabilityMeasure (countMix ρ ν) := by
  constructor
  rw [countMix_apply ρ ν MeasurableSet.univ]
  simp only [preimage_univ, measure_univ, mul_one]
  simpa using (lintegral_countable' (μ := ρ) (fun _ : ℕ => (1 : ℝ≥0∞))).symm

lemma countMix_real (ρ : Measure ℕ) (ν : Measure α)
    [IsProbabilityMeasure ρ] [IsProbabilityMeasure ν] {A : Set (Sample α)}
    (hA : MeasurableSet A) :
    (countMix ρ ν).real A = ∑' k : ℕ, ρ.real {k} *
      (Measure.pi fun _ : Fin k => ν).real ((fun x : Fin k → α => (⟨k, x⟩ : Sample α)) ⁻¹' A) := by
  rw [measureReal_def, countMix_apply ρ ν hA,
    ENNReal.tsum_toReal_eq (fun k => mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _))]
  simp only [ENNReal.toReal_mul, measureReal_def]

/-- Scaling an iid mark law scales the `k`-point product by the `k`th power. -/
lemma pi_const_smul (ν : Measure α) [IsProbabilityMeasure ν] (c : ℝ≥0∞) (hc : c ≠ ⊤)
    (k : ℕ) :
    (Measure.pi fun _ : Fin k => c • ν) = c ^ k • (Measure.pi fun _ : Fin k => ν) := by
  have : IsFiniteMeasure (c • ν) := ⟨by simpa using hc.lt_top⟩
  refine Measure.pi_eq fun s hs => ?_
  rw [Measure.smul_apply, Measure.pi_pi, smul_eq_mul]
  simp only [Measure.smul_apply, smul_eq_mul]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- Identification with the previously constructed Poisson point process, including rate zero. -/
theorem countMix_poisson (ν : Measure α) [IsProbabilityMeasure ν] (r : ℝ≥0) :
    countMix (ProbabilityTheory.poissonMeasure r) ν = law ((r : ℝ≥0∞) • ν) := by
  unfold countMix law
  congr 1
  funext k
  rw [ProbabilityTheory.poissonMeasure_singleton,
    pi_const_smul ν (r : ℝ≥0∞) (by simp) k, Measure.map_smul _ (measurable_sampleMk k).aemeasurable,
    smul_smul]
  congr 1
  have he : w0 ((r : ℝ≥0∞) • ν) = ENNReal.ofReal (Real.exp (-(r : ℝ))) := by
    simp [w0, Measure.smul_apply]
  rw [he, ENNReal.ofReal_div_of_pos (show (0 : ℝ) < k.factorial by positivity),
    ENNReal.ofReal_mul (Real.exp_pos _).le]
  simp only [← NNReal.coe_pow, ENNReal.ofReal_coe_nnreal, ENNReal.coe_pow,
    ENNReal.ofReal_natCast]
  simp only [ENNReal.div_eq_inv_mul]
  ring

/-- Fixed-window binomial events converge to actual probabilities in the finite Poisson law.
The conditional mark/event convergence is required at every fixed count. -/
theorem marked_binomial_event_limit {p : ℕ → unitInterval} {r : ℝ≥0}
    (ν : Measure α) [IsProbabilityMeasure ν]
    (νn : ℕ → Measure α) [∀ n, IsProbabilityMeasure (νn n)]
    {A : ℕ → Set (Sample α)} {B : Set (Sample α)}
    (hA : ∀ n, MeasurableSet (A n)) (hB : MeasurableSet B)
    (hr : Tendsto (fun n : ℕ => (n : ℝ) * (p n : ℝ)) atTop (𝓝 (r : ℝ)))
    (hmarks : ∀ k : ℕ, Tendsto
      (fun n => (Measure.pi fun _ : Fin k => νn n).real ((fun x : Fin k → α => (⟨k, x⟩ : Sample α)) ⁻¹' A n))
      atTop (𝓝 ((Measure.pi fun _ : Fin k => ν).real ((fun x : Fin k → α => (⟨k, x⟩ : Sample α)) ⁻¹' B)))) :
    Tendsto (fun n => (countMix (ProbabilityTheory.binomial n (p n)) (νn n)).real (A n))
      atTop (𝓝 ((law ((r : ℝ≥0∞) • ν)).real B)) := by
  rw [← countMix_poisson ν r, countMix_real _ ν hB]
  simp_rw [countMix_real _ _ (hA _)]
  exact binomial_mass_average hr
    (fun n k => by rw [abs_of_nonneg measureReal_nonneg]; exact measureReal_le_one) hmarks

end PoissonPP
