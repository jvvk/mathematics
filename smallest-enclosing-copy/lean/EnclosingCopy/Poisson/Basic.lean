import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Poisson point processes with finite intensity

Mathlib has the Poisson distribution on `ℕ` but no point processes. We define the Poisson process
with a finite intensity measure `Λ` on a measurable space `α` through its law, the classical
mixed-binomial construction: draw `N ~ Poisson(Λ(α))`, then `N` independent points with law
`Λ / Λ(α)`. A configuration is the multiset of its points. Written without normalising, the
expectation of a functional `G` of the configuration is

  `E[G(Π)] = ∑ₙ e^{-Λ(α)} / n! · ∫ G({x₁, …, xₙ}) dΛⁿ(x)`.

* `expect_one`: total mass one.
* `void_prob`: the void probability `P(Π ∩ B = ∅) = exp(-Λ(B))`.
-/

namespace PoissonPP

open MeasureTheory ENNReal Set

variable {α : Type*} [MeasurableSpace α]

/-- The Poisson weight `e^{-Λ(α)}`. -/
noncomputable def w0 (Λ : Measure α) : ℝ≥0∞ := ENNReal.ofReal (Real.exp (-(Λ univ).toReal))

/-- The configuration of the points `x₀, …, x_{n-1}`. -/
def config {n : ℕ} (x : Fin n → α) : Multiset α := Finset.univ.val.map x

/-- **The Poisson process with intensity `Λ`**, through the expectations of its functionals. -/
noncomputable def expect (Λ : Measure α) (G : Multiset α → ℝ≥0∞) : ℝ≥0∞ :=
  ∑' n : ℕ, w0 Λ / n.factorial * ∫⁻ x : Fin n → α, G (config x) ∂(Measure.pi fun _ => Λ)

/-- The probability of an event of the configuration. -/
noncomputable def prob (Λ : Measure α) (E : Multiset α → Prop) : ℝ≥0∞ :=
  expect Λ fun l => {l | E l}.indicator (1 : Multiset α → ℝ≥0∞) l

omit [MeasurableSpace α] in
lemma mem_config {n : ℕ} (x : Fin n → α) (a : α) : a ∈ config x ↔ ∃ i, x i = a := by
  simp [config]

/-- The exponential series in `ℝ≥0∞`. -/
lemma tsum_pow_div_factorial {x : ℝ} (hx : 0 ≤ x) :
    ∑' n : ℕ, ENNReal.ofReal x ^ n / n.factorial = ENNReal.ofReal (Real.exp x) := by
  have hs := NormedSpace.expSeries_div_hasSum_exp (𝔸 := ℝ) x
  rw [← Real.exp_eq_exp_ℝ] at hs
  have hterm : ∀ n : ℕ, ENNReal.ofReal x ^ n / n.factorial = ENNReal.ofReal (x ^ n / n.factorial) := by
    intro n
    rw [ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_pow hx, ENNReal.ofReal_natCast]
  simp_rw [hterm]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) hs.summable, hs.tsum_eq]

variable (Λ : Measure α) [IsFiniteMeasure Λ]

lemma measure_univ_eq : Λ univ = ENNReal.ofReal (Λ univ).toReal :=
  (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm

omit [IsFiniteMeasure Λ] in
/-- `e^{-λ} · ∑ cⁿ/n! = e^{c - λ}`. -/
lemma w0_mul_tsum {c : ℝ} (hc : 0 ≤ c) :
    w0 Λ * ∑' n : ℕ, ENNReal.ofReal c ^ n / n.factorial
      = ENNReal.ofReal (Real.exp (c - (Λ univ).toReal)) := by
  rw [tsum_pow_div_factorial hc, w0, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
  ring_nf

/-- The integral of a function of the number of points only. -/
lemma lintegral_const_pi (n : ℕ) (c : ℝ≥0∞) :
    ∫⁻ _ : Fin n → α, c ∂(Measure.pi fun _ => Λ) = c * Λ univ ^ n := by
  rw [lintegral_const, ← pi_univ, Measure.pi_pi, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]

/-- **Total mass one.** -/
theorem expect_one : expect Λ (fun _ => 1) = 1 := by
  unfold expect
  have : ∀ n : ℕ, w0 Λ / n.factorial * ∫⁻ _ : Fin n → α, (1 : ℝ≥0∞) ∂(Measure.pi fun _ => Λ)
      = w0 Λ * (Λ univ ^ n / n.factorial) := by
    intro n
    rw [lintegral_const_pi, one_mul]
    simp only [ENNReal.div_eq_inv_mul]
    ring
  simp_rw [this]
  rw [ENNReal.tsum_mul_left, measure_univ_eq Λ, w0_mul_tsum Λ ENNReal.toReal_nonneg]
  simp

/-- **Void probability.** For measurable `B`, `P(Π ∩ B = ∅) = exp(-Λ(B))`. -/
theorem void_prob {B : Set α} (hB : MeasurableSet B) :
    prob Λ (fun l => ∀ x ∈ l, x ∉ B) = ENNReal.ofReal (Real.exp (-(Λ B).toReal)) := by
  unfold prob expect
  have hint : ∀ n : ℕ, ∫⁻ x : Fin n → α,
      {l : Multiset α | ∀ x ∈ l, x ∉ B}.indicator (1 : Multiset α → ℝ≥0∞) (config x)
      ∂(Measure.pi fun _ => Λ) = Λ Bᶜ ^ n := by
    intro n
    have : (fun x : Fin n → α => {l : Multiset α | ∀ x ∈ l, x ∉ B}.indicator
        (1 : Multiset α → ℝ≥0∞) (config x)) = (univ.pi fun _ => Bᶜ).indicator 1 := by
      funext x
      have hiff : config x ∈ {l : Multiset α | ∀ x ∈ l, x ∉ B} ↔ x ∈ univ.pi fun _ => Bᶜ := by
        simp [mem_config]
      by_cases h : x ∈ univ.pi fun _ => Bᶜ
      · rw [indicator_of_mem (hiff.2 h), indicator_of_mem h]; rfl
      · rw [indicator_of_notMem (fun h' => h (hiff.1 h')), indicator_of_notMem h]
    rw [this, lintegral_indicator_one (MeasurableSet.univ_pi fun _ => hB.compl), Measure.pi_pi]
    simp
  simp_rw [hint]
  have hBc : Λ Bᶜ = ENNReal.ofReal (Λ univ - Λ B).toReal := by
    rw [measure_compl hB (measure_ne_top _ _), ENNReal.ofReal_toReal (by finiteness)]
  have : ∀ n : ℕ, w0 Λ / n.factorial * Λ Bᶜ ^ n = w0 Λ * (Λ Bᶜ ^ n / n.factorial) := fun n => by
    simp only [ENNReal.div_eq_inv_mul]; ring
  simp_rw [this]
  rw [ENNReal.tsum_mul_left, hBc, w0_mul_tsum Λ ENNReal.toReal_nonneg,
    ENNReal.toReal_sub_of_le (measure_mono (subset_univ B)) (measure_ne_top _ _)]
  ring_nf

end PoissonPP
