import EnclosingCopy.Poisson.WindowLimit

/-!
# Witness-window and overlap bounds for actual iid samples

The exact iid void law gives the limiting exponential witness-window probabilities.
The union bound shows that windows with `n μ(B_n) → 0` are empty with probability tending
to one. For MO 458571 these apply once the polygon geometry establishes the areas of
side witness rectangles and of the corner overlap regions.
-/
namespace PoissonPP
open MeasureTheory Set ENNReal Filter Topology
open scoped NNReal
variable {α : Type*} [MeasurableSpace α]

/-- The exact iid void law in a measurable window. -/
theorem iid_void_prob (μ : Measure α) [IsProbabilityMeasure μ] {B : Set α}
    (hB : MeasurableSet B) (n : ℕ) :
    (Measure.pi fun _ : Fin n => μ) {x | ∀ i, x i ∉ B} = (1 - μ B) ^ n := by
  have hs : {x : Fin n → α | ∀ i, x i ∉ B} = univ.pi (fun _ => Bᶜ) := by ext; simp
  rw [hs, Measure.pi_pi]
  simp only [measure_compl hB (measure_ne_top _ _), measure_univ,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- Witness windows of mass asymptotic to `r/n` have void probability tending to `e^{-r}`. -/
theorem iid_void_limit (μ : ℕ → Measure α) [∀ n, IsProbabilityMeasure (μ n)]
    (B : ℕ → Set α) (hB : ∀ n, MeasurableSet (B n)) {r : ℝ≥0}
    (hr : Tendsto (fun n : ℕ => (n : ℝ) * (μ n).real (B n)) atTop (𝓝 (r : ℝ))) :
    Tendsto (fun n => (Measure.pi fun _ : Fin n => μ n) {x | ∀ i, x i ∉ B n})
      atTop (𝓝 (ENNReal.ofReal (Real.exp (-(r : ℝ))))) := by
  have hp n : 0 ≤ (μ n).real (B n) := measureReal_nonneg
  have hq n : (μ n).real (B n) ≤ 1 := measureReal_le_one
  have heq n : (1 - (μ n) (B n)) ^ n =
      ENNReal.ofReal ((1 - (μ n).real (B n)) ^ n) := by
    rw [ENNReal.ofReal_pow (sub_nonneg.mpr (hq n)), ENNReal.ofReal_sub 1 (hp n),
      ENNReal.ofReal_one, measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)]
  simp_rw [iid_void_prob (μ _) (hB _), heq]
  have ht := ProbabilityTheory.tendsto_choose_mul_pow_of_tendsto_mul_atTop 0 hr
  simp only [Nat.choose_zero_right, pow_zero, Nat.cast_one, one_mul,
    Nat.sub_zero, Nat.factorial_zero, div_one, mul_one] at ht
  exact ENNReal.tendsto_ofReal ht

/-- One point in the window: the finite union bound, with no independence assumption beyond
what is already built into the iid product law. -/
theorem iid_hit_le (μ : Measure α) [IsProbabilityMeasure μ] {B : Set α}
    (hB : MeasurableSet B) (n : ℕ) :
    (Measure.pi fun _ : Fin n => μ) {x | ∃ i, x i ∈ B} ≤ (n : ℝ≥0∞) * μ B := by
  have hs : {x : Fin n → α | ∃ i, x i ∈ B} = ⋃ i : Fin n, (Function.eval i) ⁻¹' B := by
    ext x; simp
  rw [hs]
  calc _ ≤ ∑ i : Fin n, (Measure.pi fun _ : Fin n => μ) ((Function.eval i) ⁻¹' B) :=
      measure_iUnion_fintype_le _ _
    _ = _ := by
      have hcoord (i : Fin n) : (Measure.pi fun _ : Fin n => μ) ((Function.eval i) ⁻¹' B) = μ B := by
        rw [← Measure.map_apply (measurable_pi_apply i) hB, Measure.pi_map_eval]
        simp
      simp only [hcoord, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- Corner overlaps of area `o(1/n)` contain no sampled point asymptotically. -/
theorem iid_hit_limit_zero (μ : ℕ → Measure α) [∀ n, IsProbabilityMeasure (μ n)]
    (B : ℕ → Set α) (hB : ∀ n, MeasurableSet (B n))
    (hr : Tendsto (fun n : ℕ => (n : ℝ) * (μ n).real (B n)) atTop (𝓝 0)) :
    Tendsto (fun n => (Measure.pi fun _ : Fin n => μ n) {x | ∃ i, x i ∈ B n})
      atTop (𝓝 0) := by
  have hb (n : ℕ) : (n : ℝ≥0∞) * (μ n) (B n) =
      ENNReal.ofReal ((n : ℝ) * (μ n).real (B n)) := by
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast, measureReal_def,
      ENNReal.ofReal_toReal (measure_ne_top _ _)]
  have ht : Tendsto (fun n : ℕ => (n : ℝ≥0∞) * (μ n) (B n)) atTop (𝓝 0) := by
    simp_rw [hb]
    simpa using ENNReal.tendsto_ofReal hr
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht
    (fun _ => zero_le) (fun n => iid_hit_le (μ n) (hB n) n)
end PoissonPP
