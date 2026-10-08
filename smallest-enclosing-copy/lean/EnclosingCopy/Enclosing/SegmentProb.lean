import EnclosingCopy.Enclosing.Segment
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# Theorem 8, segment optima: the probability that the segment meets the chord

In the segment case the free coordinate `y` must exceed the largest lower bound `ℓ` and stay below
the smallest upper bound `r`, and the event needs some feasible `y` in the chord `[α, β]`. The
bounds come from different sides, so `ℓ` and `r` are independent. The paper's formula is

  `P(ℓ ≤ β, r ≥ α, ℓ ≤ r) = F(α) G(α) + ∫_α^β G dF`,

with `F(y) = P(ℓ ≤ y)` and `G(y) = P(r ≥ y)`. This file proves it for independent real random
variables whose distribution function `F` has a continuous derivative `F'` on `[α, β]`
(`segment_event_prob`), and combines it with `segment_prob` to get the paper's closed form
`F G (1 + S (β - α))` when `F G` is constant and `F' = S F` (`segment_event_closed`).
-/

namespace Enclosing

open MeasureTheory ProbabilityTheory Set

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- The law of `ℓ` on `(α, β]` has density `F'`. -/
lemma law_restrict_eq {ℓ : Ω → ℝ} (hℓ : Measurable ℓ) {α β : ℝ} (hαβ : α ≤ β) {F F' : ℝ → ℝ}
    (hF : ∀ y ∈ Icc α β, P.real {ω | ℓ ω ≤ y} = F y) (hFc : ContinuousOn F (Icc α β))
    (hder : ∀ y ∈ Ioo α β, HasDerivAt F (F' y) y) (hF'c : Continuous F')
    (hF'0 : ∀ y ∈ Icc α β, 0 ≤ F' y) :
    (P.map ℓ).restrict (Ioc α β)
      = (volume.restrict (Ioc α β)).withDensity fun y => ENNReal.ofReal (F' y) := by
  have hmapIic : ∀ y ∈ Icc α β, P.map ℓ (Iic y) = ENNReal.ofReal (F y) := by
    intro y hy
    rw [Measure.map_apply hℓ measurableSet_Iic, ← hF y hy, measureReal_def,
      ENNReal.ofReal_toReal (measure_ne_top _ _)]
    rfl
  -- both sides agree on `Ioc c d` for `α ≤ c ≤ d ≤ β`
  have hpiece : ∀ c d, α ≤ c → c ≤ d → d ≤ β →
      P.map ℓ (Ioc c d) = ∫⁻ y in Ioc c d, ENNReal.ofReal (F' y) := by
    intro c d hc hcd hd
    have hcI : c ∈ Icc α β := ⟨hc, hcd.trans hd⟩
    have hdI : d ∈ Icc α β := ⟨hc.trans hcd, hd⟩
    have hset : Ioc c d = Iic d \ Iic c := by
      ext y; simp only [mem_Ioc, mem_diff, mem_Iic, not_le]; exact and_comm
    rw [show P.map ℓ (Ioc c d) = P.map ℓ (Iic d \ Iic c) by rw [hset], measure_diff (Iic_subset_Iic.2 hcd) measurableSet_Iic.nullMeasurableSet
      (measure_ne_top _ _), hmapIic d hdI, hmapIic c hcI]
    have hFTC : ∫ y in c..d, F' y = F d - F c :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hcd
        (hFc.mono (Icc_subset_Icc hc hd))
        (fun y hy => hder y ⟨hc.trans_lt hy.1, hy.2.trans_le hd⟩) (hF'c.intervalIntegrable _ _)
    have hnn : 0 ≤ ∫ y in c..d, F' y :=
      intervalIntegral.integral_nonneg hcd fun y hy => hF'0 y ⟨hc.trans hy.1, hy.2.trans hd⟩
    rw [← ENNReal.ofReal_sub _ (by rw [← hF c hcI]; exact measureReal_nonneg),
      ← hFTC, intervalIntegral.integral_of_le hcd, ofReal_integral_eq_lintegral_ofReal]
    · exact (hF'c.continuousOn.integrableOn_Icc (μ := volume) (a := c) (b := d)).mono_set
        Ioc_subset_Icc_self
    · exact (ae_restrict_iff' (μ := volume) measurableSet_Ioc).2 (Filter.Eventually.of_forall fun y hy =>
        hF'0 y ⟨hc.trans hy.1.le, hy.2.trans hd⟩)
  have : IsFiniteMeasure ((P.map ℓ).restrict (Ioc α β)) := inferInstance
  apply Measure.ext_of_Ioc_finite
  · rw [Measure.restrict_apply_univ, withDensity_apply _ MeasurableSet.univ,
      Measure.restrict_univ]
    exact hpiece α β le_rfl hαβ le_rfl
  · intro a b hab
    rw [Measure.restrict_apply measurableSet_Ioc, withDensity_apply _ measurableSet_Ioc,
      Measure.restrict_restrict measurableSet_Ioc, Ioc_inter_Ioc]
    by_cases h : max a α ≤ min b β
    · exact hpiece _ _ (le_max_right _ _) h (min_le_right _ _)
    · push Not at h
      rw [Ioc_eq_empty (not_lt.2 h.le), measure_empty, Measure.restrict_empty, lintegral_zero_measure]

/-- **The segment event.** For independent `ℓ, r` with `F(y) = P(ℓ ≤ y)` and `G(y) = P(r ≥ y)`
on `[α, β]`, and `F` with continuous derivative `F' ≥ 0` there,
`P(ℓ ≤ β, r ≥ α, ℓ ≤ r) = F(α) G(α) + ∫_α^β G F'`. -/
theorem segment_event_prob {ℓ r : Ω → ℝ} (hℓ : Measurable ℓ) (hr : Measurable r)
    (hind : IndepFun ℓ r P) {α β : ℝ} (hαβ : α ≤ β) {F G F' : ℝ → ℝ}
    (hF : ∀ y ∈ Icc α β, P.real {ω | ℓ ω ≤ y} = F y)
    (hG : ∀ y ∈ Icc α β, P.real {ω | y ≤ r ω} = G y)
    (hFc : ContinuousOn F (Icc α β)) (hder : ∀ y ∈ Ioo α β, HasDerivAt F (F' y) y)
    (hF'c : Continuous F') (hF'0 : ∀ y ∈ Icc α β, 0 ≤ F' y) :
    P.real {ω | ℓ ω ≤ β ∧ α ≤ r ω ∧ ℓ ω ≤ r ω} = F α * G α + ∫ y in α..β, G y * F' y := by
  set μ := P.map ℓ
  set ν := P.map r
  have hprod : P.map (fun ω => (ℓ ω, r ω)) = μ.prod ν :=
    hind.map_prod_eq_prod_map_map hℓ.aemeasurable hr.aemeasurable
  have hαI : α ∈ Icc α β := ⟨le_rfl, hαβ⟩
  have hνIci : ∀ y ∈ Icc α β, ν (Ici y) = ENNReal.ofReal (G y) := by
    intro y hy
    rw [Measure.map_apply hr measurableSet_Ici, ← hG y hy, measureReal_def,
      ENNReal.ofReal_toReal (measure_ne_top _ _)]
    rfl
  have hμIic : μ (Iic α) = ENNReal.ofReal (F α) := by
    rw [Measure.map_apply hℓ measurableSet_Iic, ← hF α hαI, measureReal_def,
      ENNReal.ofReal_toReal (measure_ne_top _ _)]
    rfl
  set S₁ : Set (ℝ × ℝ) := Iic α ×ˢ Ici α
  set S₂ : Set (ℝ × ℝ) := (Ioc α β ×ˢ univ) ∩ {p | p.1 ≤ p.2}
  have hS₁ : MeasurableSet S₁ := measurableSet_Iic.prod measurableSet_Ici
  have hS₂ : MeasurableSet S₂ :=
    (measurableSet_Ioc.prod MeasurableSet.univ).inter (measurableSet_le measurable_fst measurable_snd)
  have hE : {ω | ℓ ω ≤ β ∧ α ≤ r ω ∧ ℓ ω ≤ r ω} = (fun ω => (ℓ ω, r ω)) ⁻¹' (S₁ ∪ S₂) := by
    ext ω
    simp only [S₁, S₂, mem_setOf_eq, mem_preimage, mem_union, mem_prod, mem_Iic, mem_Ici,
      mem_inter_iff, mem_Ioc, mem_univ, and_true]
    constructor
    · rintro ⟨h1, h2, h3⟩
      by_cases h : ℓ ω ≤ α
      · exact Or.inl ⟨h, h2⟩
      · exact Or.inr ⟨⟨lt_of_not_ge h, h1⟩, h3⟩
    · rintro (⟨h1, h2⟩ | ⟨⟨h1, h2⟩, h3⟩)
      · exact ⟨h1.trans hαβ, h2, h1.trans h2⟩
      · exact ⟨h2, h1.le.trans h3, h3⟩
  have hdisj : Disjoint S₁ S₂ := by
    rw [Set.disjoint_left]
    rintro p ⟨h1, -⟩ ⟨⟨h2, -⟩, -⟩
    exact absurd (mem_Iic.1 h1) (not_le.2 (mem_Ioc.1 h2).1)
  have hmeasE : P {ω | ℓ ω ≤ β ∧ α ≤ r ω ∧ ℓ ω ≤ r ω} = μ.prod ν S₁ + μ.prod ν S₂ := by
    rw [hE, ← Measure.map_apply (hℓ.prodMk hr) (hS₁.union hS₂), hprod, measure_union hdisj hS₂]
  -- the first piece
  have h₁ : μ.prod ν S₁ = ENNReal.ofReal (F α) * ENNReal.ofReal (G α) := by
    rw [Measure.prod_prod, hμIic, hνIci α hαI]
  -- the second piece: integrate `ν (Ici l)` against the density `F'`
  have hanti : Antitone fun l => ν (Ici l) := fun a b hab => measure_mono (Ici_subset_Ici.2 hab)
  have h₂ : μ.prod ν S₂ = ENNReal.ofReal (∫ y in α..β, G y * F' y) := by
    rw [Measure.prod_apply hS₂]
    have hsec : ∀ l, ν (Prod.mk l ⁻¹' S₂) = (Ioc α β).indicator (fun l => ν (Ici l)) l := by
      intro l
      by_cases hl : l ∈ Ioc α β
      · rw [indicator_of_mem hl]; congr 1; ext s; simp [S₂, hl]
      · rw [indicator_of_notMem hl]
        convert measure_empty (μ := ν); ext s; simp [S₂, hl]
    simp_rw [hsec]
    rw [lintegral_indicator measurableSet_Ioc, law_restrict_eq hℓ hαβ hF hFc hder hF'c hF'0,
      lintegral_withDensity_eq_lintegral_mul (volume.restrict (Ioc α β))
        (f := fun y => ENNReal.ofReal (F' y)) (ENNReal.measurable_ofReal.comp hF'c.measurable)
        hanti.measurable]
    have hcongr : ∀ y ∈ Ioc α β, (fun y => ENNReal.ofReal (F' y)) y * ν (Ici y)
        = ENNReal.ofReal (G y * F' y) := by
      intro y hy
      have hyI : y ∈ Icc α β := ⟨hy.1.le, hy.2⟩
      rw [hνIci y hyI, ← ENNReal.ofReal_mul (hF'0 y hyI), mul_comm]
    simp only [Pi.mul_apply]
    rw [setLIntegral_congr_fun measurableSet_Ioc hcongr, intervalIntegral.integral_of_le hαβ]
    -- `G = ν.real (Ici ·)` on the interval, so `G F'` is integrable there
    have hGeq : ∀ y ∈ Ioc α β, G y * F' y = (ν (Ici y)).toReal * F' y := by
      intro y hy
      rw [hνIci y ⟨hy.1.le, hy.2⟩, ENNReal.toReal_ofReal (by
        rw [← hG y ⟨hy.1.le, hy.2⟩]; exact measureReal_nonneg)]
    have hint : IntegrableOn (fun y => G y * F' y) (Ioc α β) := by
      refine IntegrableOn.congr_fun ?_ (fun y hy => (hGeq y hy).symm) measurableSet_Ioc
      obtain ⟨C, hC⟩ := (isCompact_Icc (a := α) (b := β)).exists_bound_of_continuousOn
        hF'c.continuousOn
      refine Integrable.of_bound ?_ C ?_
      · exact ((ENNReal.measurable_toReal.comp hanti.measurable).mul
          hF'c.measurable).aestronglyMeasurable
      · refine (ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall fun y hy => ?_)
        have h1 : (ν (Ici y)).toReal ≤ 1 := by
          have : ν (Ici y) ≤ 1 := prob_le_one
          exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using this)
        rw [norm_mul, Real.norm_of_nonneg ENNReal.toReal_nonneg]
        calc (ν (Ici y)).toReal * ‖F' y‖ ≤ 1 * C :=
              mul_le_mul h1 (hC y ⟨hy.1.le, hy.2⟩) (norm_nonneg _) zero_le_one
          _ = C := one_mul C
    rw [ofReal_integral_eq_lintegral_ofReal hint]
    exact (ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall fun y hy =>
      mul_nonneg (by rw [← hG y ⟨hy.1.le, hy.2⟩]; exact measureReal_nonneg)
        (hF'0 y ⟨hy.1.le, hy.2⟩))
  have hFα : 0 ≤ F α := by rw [← hF α hαI]; exact measureReal_nonneg
  have hGα : 0 ≤ G α := by rw [← hG α hαI]; exact measureReal_nonneg
  have hI : 0 ≤ ∫ y in α..β, G y * F' y :=
    intervalIntegral.integral_nonneg hαβ fun y hy =>
      mul_nonneg (by rw [← hG y hy]; exact measureReal_nonneg) (hF'0 y hy)
  rw [measureReal_def, hmeasE, h₁, h₂, ← ENNReal.ofReal_mul hFα, ← ENNReal.ofReal_add
    (mul_nonneg hFα hGα) hI, ENNReal.toReal_ofReal (add_nonneg (mul_nonneg hFα hGα) hI)]

/-- **The paper's closed form.** If moreover `F G` is the constant `K₀` on the chord and
`F' = S F` (the void exponents are linear in `y`), the probability is `K₀ (1 + S (β - α))`. -/
theorem segment_event_closed {ℓ r : Ω → ℝ} (hℓ : Measurable ℓ) (hr : Measurable r)
    (hind : IndepFun ℓ r P) {α β : ℝ} (hαβ : α ≤ β) {F G F' : ℝ → ℝ} {S K₀ : ℝ}
    (hF : ∀ y ∈ Icc α β, P.real {ω | ℓ ω ≤ y} = F y)
    (hG : ∀ y ∈ Icc α β, P.real {ω | y ≤ r ω} = G y)
    (hFc : ContinuousOn F (Icc α β)) (hder : ∀ y ∈ Ioo α β, HasDerivAt F (F' y) y)
    (hF'c : Continuous F') (hF'0 : ∀ y ∈ Icc α β, 0 ≤ F' y)
    (hFG : ∀ y ∈ Icc α β, F y * G y = K₀) (hFS : ∀ y ∈ Icc α β, F' y = S * F y) :
    P.real {ω | ℓ ω ≤ β ∧ α ≤ r ω ∧ ℓ ω ≤ r ω} = K₀ * (1 + S * (β - α)) := by
  rw [segment_event_prob hℓ hr hind hαβ hF hG hFc hder hF'c hF'0]
  have : EqOn (fun y => G y * F' y) (fun _ => S * K₀) (uIcc α β) := by
    intro y hy
    rw [uIcc_of_le hαβ] at hy
    simp only
    rw [hFS y hy, ← hFG y hy]
    ring
  rw [intervalIntegral.integral_congr this, hFG α ⟨le_rfl, hαβ⟩]
  simp
  ring

end Enclosing
