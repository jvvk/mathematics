import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Section 2, heuristic made exact: the limit LP is the first-order limit of the geometry

Work in the frame of side `i`: `u` is its outward normal, `t = R_{90°} u`, so a point is
`x = (x·u, x·t)`. The copy `(1 + ε/n) R_{Θ/n} K + c/n`, with `c · u = C₁` and `c · t = C₂`.

* A vertex `w = h u + b t` of `K` (the end of side `i` at position `b`) is carried to a point whose
  `u`-coordinate is `(1 + ε/n)(h cos(Θ/n) - b sin(Θ/n)) + C₁/n`. The copy's vertex stays behind
  the line of side `i` iff this is `≤ h`. Scaled by `n`, the excess tends to `ε h + C₁ - Θ b`
  (`vertex_limit`). With both ends `a` and `b`, the copy fits at side `i` in the limit iff
  `ε h + C₁ ≤ min (Θ a) (Θ b)`: the event `E` of the limit model.
* A sample point `x = (h - D/n) u + s t` lies in the copy iff its support in the rotated normal
  direction is at most the copy's: `(h - D/n) cos(Θ/n) + s sin(Θ/n) ≤ (1 + ε/n) h + c · R_{Θ/n} u`
  (Step 2). Scaled by `n`, the slack tends to `ε h + C₁ - Θ s + D` (`point_limit`), the limit LP
  constraint `Hᵢ ≥ Θ s - D`.

The rotation enters only through `n sin(Θ/n) → Θ` and `n (1 - cos(Θ/n)) → 0`.
-/

namespace Enclosing

open Filter Topology Real

/-- `n sin(Θ/n) → Θ`. -/
lemma tendsto_n_sin (Θ : ℝ) : Tendsto (fun n : ℕ => (n : ℝ) * sin (Θ / n)) atTop (𝓝 Θ) := by
  rcases eq_or_ne Θ 0 with rfl | hΘ
  · simp
  have hsinc : Tendsto (fun x : ℝ => sin x / x) (𝓝[≠] 0) (𝓝 1) := by
    simpa [div_eq_inv_mul] using (hasDerivAt_sin 0).tendsto_slope_zero
  have hx : Tendsto (fun n : ℕ => Θ / (n : ℝ)) atTop (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · simpa using tendsto_const_div_atTop_nhds_zero_nat Θ
    · filter_upwards [eventually_gt_atTop 0] with n hn
      exact div_ne_zero hΘ (by exact_mod_cast hn.ne')
  have := (hsinc.comp hx).const_mul Θ
  rw [mul_one] at this
  refine this.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  simp only [Function.comp]
  field_simp

/-- `n (1 - cos(Θ/n)) → 0`. -/
lemma tendsto_n_one_sub_cos (Θ : ℝ) :
    Tendsto (fun n : ℕ => (n : ℝ) * (1 - cos (Θ / n))) atTop (𝓝 0) := by
  -- `0 ≤ 1 - cos x ≤ x²/2`
  have hb : ∀ n : ℕ, 0 < n → |(n : ℝ) * (1 - cos (Θ / n))| ≤ Θ ^ 2 / 2 / n := by
    intro n hn
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have h1 : 0 ≤ 1 - cos (Θ / n) := by linarith [cos_le_one (Θ / n)]
    have h2 : 1 - cos (Θ / n) ≤ (Θ / n) ^ 2 / 2 := by linarith [one_sub_sq_div_two_le_cos (x := Θ / n)]
    rw [abs_of_nonneg (by positivity)]
    calc (n : ℝ) * (1 - cos (Θ / n)) ≤ n * ((Θ / n) ^ 2 / 2) := by gcongr
      _ = Θ ^ 2 / 2 / n := by field_simp
  have hlim : Tendsto (fun n : ℕ => Θ ^ 2 / 2 / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat _
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [eventually_gt_atTop 0] with n hn
  exact hb n hn

/-- **The vertex constraint, linearised.** -/
theorem vertex_limit (ε h b C₁ Θ : ℝ) :
    Tendsto (fun n : ℕ => (n : ℝ) *
        ((1 + ε / n) * (h * cos (Θ / n) - b * sin (Θ / n)) + C₁ / n - h)) atTop
      (𝓝 (ε * h + C₁ - Θ * b)) := by
  have hc : Tendsto (fun n : ℕ => cos (Θ / (n : ℝ))) atTop (𝓝 1) := by
    have := (continuous_cos.tendsto 0).comp (tendsto_const_div_atTop_nhds_zero_nat Θ)
    simpa [Function.comp_def] using this
  have hs : Tendsto (fun n : ℕ => sin (Θ / (n : ℝ))) atTop (𝓝 0) := by
    have := (continuous_sin.tendsto 0).comp (tendsto_const_div_atTop_nhds_zero_nat Θ)
    simpa [Function.comp_def] using this
  -- `n(...) = -h·n(1 - cos) - b·n sin + ε (h cos - b sin) + C₁`
  have hlim := ((((tendsto_n_one_sub_cos Θ).const_mul (-h)).sub
    ((tendsto_n_sin Θ).const_mul b)).add (((hc.const_mul h).sub (hs.const_mul b)).const_mul ε)).add_const C₁
  rw [show ε * h + C₁ - Θ * b = -h * 0 - b * Θ + ε * (h * 1 - b * 0) + C₁ by ring]
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  field_simp
  ring

/-- **The point constraint, linearised.** The copy's support in the rotated normal direction,
`(1 + ε/n) h + c · R_{Θ/n} u` with `c · u = C₁/n`, `c · t = C₂/n`, minus the point's support
`(h - D/n) cos(Θ/n) + s sin(Θ/n)`, scaled by `n`, tends to `ε h + C₁ - Θ s + D`. -/
theorem point_limit (ε h s D C₁ C₂ Θ : ℝ) :
    Tendsto (fun n : ℕ => (n : ℝ) *
        ((1 + ε / n) * h + (C₁ / n * cos (Θ / n) + C₂ / n * sin (Θ / n))
          - ((h - D / n) * cos (Θ / n) + s * sin (Θ / n)))) atTop
      (𝓝 (ε * h + C₁ - Θ * s + D)) := by
  have hc : Tendsto (fun n : ℕ => cos (Θ / (n : ℝ))) atTop (𝓝 1) := by
    have := (continuous_cos.tendsto 0).comp (tendsto_const_div_atTop_nhds_zero_nat Θ)
    simpa [Function.comp_def] using this
  have hs : Tendsto (fun n : ℕ => sin (Θ / (n : ℝ))) atTop (𝓝 0) := by
    have := (continuous_sin.tendsto 0).comp (tendsto_const_div_atTop_nhds_zero_nat Θ)
    simpa [Function.comp_def] using this
  have hlim := ((((tendsto_n_one_sub_cos Θ).const_mul h).sub ((tendsto_n_sin Θ).const_mul s)).add
    (((hc.const_mul C₁).add (hs.const_mul C₂)).add ((hc.const_mul D)))).add_const (ε * h)
  rw [show ε * h + C₁ - Θ * s + D = h * 0 - s * Θ + (C₁ * 1 + C₂ * 0 + D * 1) + ε * h by ring]
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  field_simp
  ring

/-- **The event `E` at one side.** If the limits at both ends are strictly negative, the copy's
two vertices on side `i` are strictly inside the line of side `i` for all large `n`; if either
limit is strictly positive, a vertex pokes out for all large `n`. -/
theorem vertex_event (ε h a b C₁ Θ : ℝ) :
    (ε * h + C₁ < min (Θ * a) (Θ * b) →
      ∀ᶠ n : ℕ in atTop, ∀ e ∈ ({a, b} : Set ℝ),
        (1 + ε / n) * (h * cos (Θ / n) - e * sin (Θ / n)) + C₁ / n < h) ∧
    (min (Θ * a) (Θ * b) < ε * h + C₁ →
      ∀ᶠ n : ℕ in atTop, ∃ e ∈ ({a, b} : Set ℝ),
        h < (1 + ε / n) * (h * cos (Θ / n) - e * sin (Θ / n)) + C₁ / n) := by
  have key : ∀ e, ε * h + C₁ - Θ * e < 0 → ∀ᶠ n : ℕ in atTop,
      (1 + ε / n) * (h * cos (Θ / n) - e * sin (Θ / n)) + C₁ / n < h := by
    intro e he
    filter_upwards [(vertex_limit ε h e C₁ Θ).eventually (gt_mem_nhds he),
      eventually_gt_atTop 0] with n hn hpos
    have : (0 : ℝ) < n := by exact_mod_cast hpos
    nlinarith
  have key' : ∀ e, 0 < ε * h + C₁ - Θ * e → ∀ᶠ n : ℕ in atTop,
      h < (1 + ε / n) * (h * cos (Θ / n) - e * sin (Θ / n)) + C₁ / n := by
    intro e he
    filter_upwards [(vertex_limit ε h e C₁ Θ).eventually (lt_mem_nhds he),
      eventually_gt_atTop 0] with n hn hpos
    have : (0 : ℝ) < n := by exact_mod_cast hpos
    nlinarith
  constructor
  · intro hlt
    have ha := key a (by linarith [min_le_left (Θ * a) (Θ * b)])
    have hb := key b (by linarith [min_le_right (Θ * a) (Θ * b)])
    filter_upwards [ha, hb] with n h1 h2
    rintro e (rfl | rfl)
    · exact h1
    · exact h2
  · intro hgt
    rcases min_choice (Θ * a) (Θ * b) with hm | hm
    · filter_upwards [key' a (by linarith)] with n h1
      exact ⟨a, by simp, h1⟩
    · filter_upwards [key' b (by linarith)] with n h1
      exact ⟨b, by simp, h1⟩

end Enclosing
