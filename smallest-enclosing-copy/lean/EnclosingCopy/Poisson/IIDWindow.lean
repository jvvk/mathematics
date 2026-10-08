import EnclosingCopy.Poisson.MarkedWindow
import EnclosingCopy.Poisson.Superpose

/-!
# Restricting an actual iid sample to a measurable window

The window restriction of `n` iid points has binomial count and iid conditional marks.
This is proved by expanding the product measure over the window and its complement,
then deleting the complement points. Combined with `MarkedWindow`, this connects the
rare-window Poisson approximation to actual fixed-size iid samples.
-/
namespace PoissonPP
open MeasureTheory Set ENNReal Filter
variable {α : Type*} [MeasurableSpace α]

/-- Keep precisely the points in the observation window. -/
noncomputable def inWindow (B : Set α) (c : Multiset α) : Multiset α := by
  classical
  exact c.filter (· ∈ B)

lemma ae_config_in (μ : Measure α) [IsFiniteMeasure μ] {B : Set α}
    (hB : MeasurableSet B) (k : ℕ) :
    ∀ᵐ x : Fin k → α ∂(Measure.pi fun _ => μ.restrict B), ∀ p ∈ config x, p ∈ B := by
  have h : ∀ᵐ x : Fin k → α ∂(Measure.pi fun _ => μ.restrict B), ∀ i, x i ∈ B :=
    eventually_all.2 fun i => Measure.tendsto_eval_ae_ae.eventually (ae_restrict_mem hB)
  filter_upwards [h] with x hx
  rintro p hp
  obtain ⟨i, rfl⟩ := (mem_config x p).mp hp
  exact hx i

lemma ae_window_pair (μ : Measure α) [IsFiniteMeasure μ] {B : Set α}
    (hB : MeasurableSet B) (j k : ℕ) (G : Multiset α → ℝ≥0∞) :
    ∀ᵐ x : Fin j → α ∂(Measure.pi fun _ => μ.restrict B),
    ∀ᵐ y : Fin k → α ∂(Measure.pi fun _ => μ.restrict Bᶜ),
      G (inWindow B (config x + config y)) = G (config x) := by
  classical
  filter_upwards [ae_config_in μ hB j] with x hx
  filter_upwards [ae_config_in μ hB.compl k] with y hy
  have hxf : inWindow B (config x) = config x := Multiset.filter_eq_self.mpr hx
  have hyf : inWindow B (config y) = 0 := Multiset.filter_eq_nil.mpr hy
  simp only [inWindow, Multiset.filter_add] at hxf hyf ⊢
  rw [hxf, hyf, add_zero]

/-- Exact binomial mixture formula for a window of an iid sample. `ν` is the conditional law
inside the window; the identity `μ.restrict B = p • ν` makes this normalization explicit. -/
theorem iid_window_expect (μ ν : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {B : Set α} (hB : MeasurableSet B) (p : unitInterval)
    (hν : μ.restrict B = ENNReal.ofReal (p : ℝ) • ν)
    (G : Multiset α → ℝ≥0∞) (hG : ConfMeas G)
    (hGB : ConfMeas (fun c => G (inWindow B c))) (n : ℕ) :
    (∫⁻ x : Fin n → α, G (inWindow B (config x)) ∂(Measure.pi fun _ => μ)) =
      ∑ k ∈ Finset.range (n + 1), (ProbabilityTheory.binomial n p) {k} *
        ∫⁻ x : Fin k → α, G (config x) ∂(Measure.pi fun _ => ν) := by
  have hmass : μ B = ENNReal.ofReal (p : ℝ) := by
    have := congrArg (fun ρ : Measure α => ρ univ) hν
    simpa using this
  have hcomp : μ Bᶜ = ENNReal.ofReal (1 - (p : ℝ)) := by
    rw [measure_compl hB (measure_ne_top _ _), measure_univ, hmass]
    rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub 1 p.2.1]
  have hpair (j k : ℕ) :
      pairInt (μ.restrict B) (μ.restrict Bᶜ) (fun c => G (inWindow B c)) j k =
        ENNReal.ofReal (p : ℝ) ^ j * ENNReal.ofReal (1 - (p : ℝ)) ^ k *
          ∫⁻ x : Fin j → α, G (config x) ∂(Measure.pi fun _ => ν) := by
    unfold pairInt
    have he := ae_window_pair μ hB j k G
    calc _ = ∫⁻ x : Fin j → α, ∫⁻ _ : Fin k → α, G (config x)
          ∂(Measure.pi fun _ => μ.restrict Bᶜ) ∂(Measure.pi fun _ => μ.restrict B) := by
            apply lintegral_congr_ae
            filter_upwards [he] with x hx
            exact lintegral_congr_ae hx
      _ = _ := by
        simp_rw [lintegral_const_pi, Measure.restrict_apply_univ, hcomp]
        rw [hν, pi_const_smul ν _ (by simp) j, lintegral_smul_measure]
        rw [lintegral_mul_const _ (hG j)]
        ring
  rw [← Measure.restrict_add_restrict_compl (μ := μ) hB,
    lintegral_pi_add (μ.restrict B) (μ.restrict Bᶜ) n _ hGB]
  simp_rw [hpair]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun j k => (n.choose j : ℝ≥0∞) *
      (ENNReal.ofReal (p : ℝ) ^ j * ENNReal.ofReal (1 - (p : ℝ)) ^ k *
        ∫⁻ x : Fin j → α, G (config x) ∂(Measure.pi fun _ => ν))) n]
  apply Finset.sum_congr rfl
  intro k hk
  rw [ProbabilityTheory.binomial_singleton]
  have hp : 0 ≤ (p : ℝ) := p.2.1
  have hpc : 0 ≤ 1 - (p : ℝ) := sub_nonneg.mpr p.2.2
  rw [ENNReal.ofReal_mul (mul_nonneg (by positivity) (pow_nonneg hp _)),
    ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast,
    ENNReal.ofReal_pow hp, ENNReal.ofReal_pow hpc]
  ring

/-- The same exact law expressed using the established marked-count probability space. -/
theorem iid_window_prob (μ ν : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {B : Set α} (hB : MeasurableSet B) (p : unitInterval)
    (hν : μ.restrict B = ENNReal.ofReal (p : ℝ) • ν)
    (E : Multiset α → Prop)
    (hE : ∀ k, MeasurableSet {x : Fin k → α | E (config x)})
    (hEB : ∀ k, MeasurableSet {x : Fin k → α | E (inWindow B (config x))}) (n : ℕ) :
    (Measure.pi fun _ : Fin n => μ) {x | E (inWindow B (config x))} =
      countMix (ProbabilityTheory.binomial n p) ν {ω | E (config ω.2)} := by
  have hA : MeasurableSet {ω : Sample α | E (config ω.2)} := measurableSet_sample hE
  rw [← lintegral_indicator_one (hEB n)]
  have h := iid_window_expect μ ν hB p hν
    ({c | E c}.indicator (1 : Multiset α → ℝ≥0∞))
    (fun k => measurable_one.indicator (hE k))
    (fun k => measurable_one.indicator (hEB k)) n
  change (∫⁻ x : Fin n → α,
    {c | E c}.indicator (1 : Multiset α → ℝ≥0∞) (inWindow B (config x))
      ∂(Measure.pi fun _ => μ)) = _
  rw [h, countMix_apply _ _ hA]
  have hi : ∀ k, (∫⁻ x : Fin k → α,
      {c | E c}.indicator (1 : Multiset α → ℝ≥0∞) (config x)
        ∂(Measure.pi fun _ => ν)) = (Measure.pi fun _ : Fin k => ν) {x | E (config x)} :=
    fun k => lintegral_indicator_one (hE k)
  simp_rw [hi]
  symm
  apply tsum_eq_sum
  intro k hk
  have hnk : n < k := by simpa using hk
  rw [ProbabilityTheory.binomial_singleton, Nat.choose_eq_zero_of_lt hnk]
  simp

end PoissonPP
