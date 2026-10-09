import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

/-!
# Unit hexagons: adjacent turns (Lemma 2.1)

Normalise three consecutive unit edges of a polygon with two positive turns as
`P₀ = (0,0)`, `P₁ = (1,0)`, `P₂ = (1 - cos α, sin α)` and
`P₃ = P₂ + (cos (α+β), -sin (α+β))`, where `α, β ∈ (0, π/2]` are the smaller angles at `P₁, P₂`.
If `2α + β ≤ π` and `α + 2β ≤ π`, the third edge meets the first at the explicit parameters
`s = sin α / sin (α+β)` on `P₂P₃` and `x = 1 - sin β / sin (α+β)` on `P₀P₁`, both in `[0,1]`.
Simplicity therefore forces `max (2α+β) (α+2β) > π`, hence `α + β > π/2` and `max α β > π/3`.
-/

open Real

namespace UnitHexagon

/-- `sin y ≤ sin (y + z)` when `0 ≤ z` and `2y + z ≤ π` with `0 ≤ y`. -/
lemma sin_le_sin_add {y z : ℝ} (hy : 0 ≤ y) (hz : 0 ≤ z) (h : 2 * y + z ≤ π) :
    Real.sin y ≤ Real.sin (y + z) := by
  have key : Real.sin (y + z) - Real.sin y = 2 * Real.sin (z / 2) * Real.cos ((2 * y + z) / 2) := by
    rw [Real.sin_sub_sin]; ring_nf
  have h1 : 0 ≤ Real.sin (z / 2) := Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
  have h2 : 0 ≤ Real.cos ((2 * y + z) / 2) :=
    Real.cos_nonneg_of_neg_pi_div_two_le_of_le (by linarith) (by linarith)
  nlinarith [mul_nonneg h1 h2]

/-- The meeting point of the first and third edges when both turn inequalities fail. -/
theorem third_edge_meets_first {α β : ℝ} (ha : 0 < α) (hb : 0 < β)
    (h1 : 2 * α + β ≤ π) (h2 : α + 2 * β ≤ π) :
    ∃ s x : ℝ, 0 ≤ s ∧ s ≤ 1 ∧ 0 ≤ x ∧ x ≤ 1 ∧
      1 - Real.cos α + s * Real.cos (α + β) = x ∧ Real.sin α - s * Real.sin (α + β) = 0 := by
  have hpos : 0 < Real.sin (α + β) := Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have hsa : Real.sin α ≤ Real.sin (α + β) := sin_le_sin_add ha.le hb.le h1
  have hsb : Real.sin β ≤ Real.sin (α + β) := by
    rw [add_comm]; exact sin_le_sin_add hb.le ha.le (by linarith)
  have hα0 : 0 ≤ Real.sin α := Real.sin_nonneg_of_nonneg_of_le_pi ha.le (by linarith)
  have hβ0 : 0 ≤ Real.sin β := Real.sin_nonneg_of_nonneg_of_le_pi hb.le (by linarith)
  refine ⟨Real.sin α / Real.sin (α + β), 1 - Real.sin β / Real.sin (α + β),
    div_nonneg hα0 hpos.le, (div_le_one hpos).2 hsa, ?_, ?_, ?_, ?_⟩
  · have := (div_le_one hpos).2 hsb; linarith
  · have := div_nonneg hβ0 hpos.le; linarith
  · field_simp
    rw [Real.sin_add, Real.cos_add]
    linear_combination (-Real.sin β) * Real.sin_sq_add_cos_sq α
  · field_simp; ring

/-- Lemma 2.1: if the first and third edges are disjoint, then `max (2α+β) (α+2β) > π`. -/
theorem adjacent_turns {α β : ℝ} (ha : 0 < α) (hb : 0 < β)
    (hdisj : ∀ s x : ℝ, 0 ≤ s → s ≤ 1 → 0 ≤ x → x ≤ 1 →
      ¬ (1 - Real.cos α + s * Real.cos (α + β) = x ∧ Real.sin α - s * Real.sin (α + β) = 0)) :
    π < max (2 * α + β) (α + 2 * β) := by
  by_contra hc
  push Not at hc
  obtain ⟨s, x, h0, h1, h2, h3, e1, e2⟩ :=
    third_edge_meets_first ha hb ((le_max_left _ _).trans hc) ((le_max_right _ _).trans hc)
  exact hdisj s x h0 h1 h2 h3 ⟨e1, e2⟩

/-- Consequences of Lemma 2.1 for angles in `(0, π/2]`. -/
theorem angle_sum_of_turns {α β : ℝ} (ha' : α ≤ π / 2) (hb' : β ≤ π / 2)
    (h : π < max (2 * α + β) (α + 2 * β)) : π / 2 < α + β ∧ π / 3 < max α β := by
  constructor
  · rcases le_total (2 * α + β) (α + 2 * β) with hle | hle
    · rw [max_eq_right hle] at h; linarith
    · rw [max_eq_left hle] at h; linarith
  · by_contra hc
    push Not at hc
    have := le_max_left α β; have := le_max_right α β
    rcases le_total (2 * α + β) (α + 2 * β) with hle | hle
    · rw [max_eq_right hle] at h; linarith
    · rw [max_eq_left hle] at h; linarith

end UnitHexagon
