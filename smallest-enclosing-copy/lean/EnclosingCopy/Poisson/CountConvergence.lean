import Mathlib.Probability.Distributions.Poisson.PoissonLimitThm
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

/-!
# Rare-window counts and bounded configuration events

Pointwise convergence of probability masses, with no loss of mass, gives convergence of
absolute differences in sum. Bounded conditional probabilities may vary with sample size.
This supplies the count part of the fixed-window Poisson approximation for MO 458571.
-/
namespace PoissonPP
open MeasureTheory Filter Topology
open scoped NNReal

lemma hasSum_mass {β : Type*} [Countable β] [MeasurableSpace β]
    [MeasurableSingletonClass β] (μ : Measure β) [IsProbabilityMeasure μ] :
    HasSum (fun k => μ.real {k}) 1 := by
  have hs : ∑' k : β, μ {k} = 1 := by
    simpa using (lintegral_countable' (μ := μ) (fun _ : β => (1 : ENNReal))).symm
  have hsum := ENNReal.summable_toReal (show ∑' k : β, μ {k} ≠ ⊤ by rw [hs]; simp)
  have ht : ∑' k : β, μ.real {k} = 1 := by
    change (∑' k : β, (μ {k}).toReal) = 1
    rw [← ENNReal.tsum_toReal_eq (fun k => measure_ne_top μ {k}), hs]
    simp
  exact ht ▸ hsum.hasSum

/-- Discrete Scheffe lemma. -/
theorem tendsto_mass_l1 {β : Type*} {w : ℕ → β → ℝ} {v : β → ℝ}
    (hw0 : ∀ n k, 0 ≤ w n k) (hv0 : ∀ k, 0 ≤ v k)
    (hw : ∀ n, HasSum (w n) 1) (hv : HasSum v 1)
    (hlim : ∀ k, Tendsto (fun n => w n k) atTop (𝓝 (v k))) :
    Tendsto (fun n => ∑' k, |w n k - v k|) atTop (𝓝 0) := by
  have hmin : Tendsto (fun n => ∑' k, min (w n k) (v k)) atTop (𝓝 1) := by
    rw [← hv.tsum_eq]
    refine tendsto_tsum_of_dominated_convergence hv.summable (fun k => ?_)
      (Eventually.of_forall fun n k => ?_)
    · simpa only [min_self] using (hlim k).min (tendsto_const_nhds (x := v k))
    · rw [Real.norm_eq_abs, abs_of_nonneg (le_min (hw0 n k) (hv0 k))]
      exact min_le_right _ _
  have heq : ∀ n, (∑' k, |w n k - v k|) = 2 - 2 * ∑' k, min (w n k) (v k) := by
    intro n
    have hm : Summable (fun k => min (w n k) (v k)) :=
      hv.summable.of_nonneg_of_le (fun k => le_min (hw0 n k) (hv0 k))
        (fun k => min_le_right _ _)
    have ha : (fun k => |w n k - v k|) =
        fun k => (w n k + v k) - 2 * min (w n k) (v k) := by
      funext k
      rcases le_total (w n k) (v k) with h | h
      · rw [min_eq_left h, abs_of_nonpos (sub_nonpos.mpr h)]; ring
      · rw [min_eq_right h, abs_of_nonneg (sub_nonneg.mpr h)]; ring
    rw [ha, ((hw n).summable.add hv.summable).tsum_sub (hm.mul_left 2),
      (hw n).summable.tsum_add hv.summable, (hw n).tsum_eq, hv.tsum_eq, tsum_mul_left]
    ring
  simpa only [heq, mul_one, sub_self] using
    (tendsto_const_nhds (x := (2 : ℝ))).sub (hmin.const_mul 2)

/-- Transfer bounded conditional probabilities that may vary with `n`. -/
theorem tendsto_mass_average {β : Type*} {w : ℕ → β → ℝ} {v : β → ℝ}
    (hw0 : ∀ n k, 0 ≤ w n k) (hv0 : ∀ k, 0 ≤ v k)
    (hw : ∀ n, HasSum (w n) 1) (hv : HasSum v 1)
    (hlim : ∀ k, Tendsto (fun n => w n k) atTop (𝓝 (v k)))
    {q : ℕ → β → ℝ} {qlim : β → ℝ} (hq : ∀ n k, |q n k| ≤ 1)
    (hqlim : ∀ k, Tendsto (fun n => q n k) atTop (𝓝 (qlim k))) :
    Tendsto (fun n => ∑' k, w n k * q n k) atTop (𝓝 (∑' k, v k * qlim k)) := by
  have hvq : Tendsto (fun n => ∑' k, v k * q n k) atTop (𝓝 (∑' k, v k * qlim k)) :=
    tendsto_tsum_of_dominated_convergence hv.summable
      (fun k => (hqlim k).const_mul (v k))
      (Eventually.of_forall fun n k => by
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hv0 k)]
        simpa only [mul_one] using mul_le_mul_of_nonneg_left (hq n k) (hv0 k))
  have hsw (n : ℕ) : Summable (fun k => w n k * q n k) :=
    (hw n).summable.of_norm_bounded (fun k => by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hw0 n k)]
      simpa only [mul_one] using mul_le_mul_of_nonneg_left (hq n k) (hw0 n k))
  have hsv (n : ℕ) : Summable (fun k => v k * q n k) :=
    hv.summable.of_norm_bounded (fun k => by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hv0 k)]
      simpa only [mul_one] using mul_le_mul_of_nonneg_left (hq n k) (hv0 k))
  have hsd (n : ℕ) : Summable (fun k => |w n k - v k|) :=
    ((hw n).summable.sub hv.summable).abs
  have hd : Tendsto (fun n => (∑' k, w n k * q n k) - ∑' k, v k * q n k)
      atTop (𝓝 0) := by
    refine squeeze_zero_norm (fun n => ?_) (tendsto_mass_l1 hw0 hv0 hw hv hlim)
    rw [← (hsw n).tsum_sub (hsv n)]
    refine (norm_tsum_le_tsum_norm ((hsw n).sub (hsv n)).norm).trans ?_
    apply Summable.tsum_le_tsum _ ((hsw n).sub (hsv n)).norm (hsd n)
    intro k
    rw [← sub_mul, Real.norm_eq_abs, abs_mul]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (hq n k) (abs_nonneg _)
  simpa only [sub_add_cancel, zero_add] using hd.add hvq

/-- Binomial rare-window counts converge in the sum of absolute mass differences. -/
theorem binomial_mass_l1 {p : ℕ → unitInterval} {r : ℝ≥0}
    (hr : Tendsto (fun n : ℕ => (n : ℝ) * (p n : ℝ)) atTop (𝓝 (r : ℝ))) :
    Tendsto (fun n => ∑' k : ℕ,
      |(ProbabilityTheory.binomial n (p n)).real {k} -
        (ProbabilityTheory.poissonMeasure r).real {k}|) atTop (𝓝 0) := by
  refine tendsto_mass_l1 (fun _ _ => measureReal_nonneg) (fun _ => measureReal_nonneg)
    (fun n => hasSum_mass (ProbabilityTheory.binomial n (p n)))
    (hasSum_mass (ProbabilityTheory.poissonMeasure r)) ?_
  intro k
  simp only [ProbabilityTheory.binomial_real_singleton,
    ProbabilityTheory.poissonMeasure_real_singleton]
  exact ProbabilityTheory.tendsto_choose_mul_pow_of_tendsto_mul_atTop k hr

/-- Transfer varying bounded conditional configuration probabilities to Poisson counts. -/
theorem binomial_mass_average {p : ℕ → unitInterval} {r : ℝ≥0}
    (hr : Tendsto (fun n : ℕ => (n : ℝ) * (p n : ℝ)) atTop (𝓝 (r : ℝ)))
    {q : ℕ → ℕ → ℝ} {qlim : ℕ → ℝ} (hq : ∀ n k, |q n k| ≤ 1)
    (hqlim : ∀ k, Tendsto (fun n => q n k) atTop (𝓝 (qlim k))) :
    Tendsto (fun n => ∑' k : ℕ, (ProbabilityTheory.binomial n (p n)).real {k} * q n k)
      atTop (𝓝 (∑' k : ℕ, (ProbabilityTheory.poissonMeasure r).real {k} * qlim k)) := by
  refine tendsto_mass_average (fun _ _ => measureReal_nonneg) (fun _ => measureReal_nonneg)
    (fun n => hasSum_mass (ProbabilityTheory.binomial n (p n)))
    (hasSum_mass (ProbabilityTheory.poissonMeasure r)) ?_ hq hqlim
  intro k
  simp only [ProbabilityTheory.binomial_real_singleton,
    ProbabilityTheory.poissonMeasure_real_singleton]
  exact ProbabilityTheory.tendsto_choose_mul_pow_of_tendsto_mul_atTop k hr
end PoissonPP
