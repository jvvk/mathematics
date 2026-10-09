import LeanProofs.UnitHexagon.Turns
import Mathlib.Analysis.Normed.Affine.Convex

/-!
# Unit hexagons: four consecutive unit hull edges (Lemma 2.3)

Normalise a convex chain of four unit edges as `P₀ = (0,0)`, `P₁ = (1,0)`, with middle interior angles
`α, β, γ ∈ (0, π/2]` and `S = α + β + γ`. The edge vectors are `(1,0)`, `(-cos α, sin α)`,
`(cos (α+β), -sin (α+β))` and `(-cos S, sin S)`. Closing the chain by `P₄P₀`, the cross products at the two
endpoints are
* at `P₀`: `sin α - sin (α+β) + sin S`;
* at `P₄`: `sin γ - sin (β+γ) + sin S`.

Convexity makes both nonnegative. When `S > π`, the one with the smaller outer angle is negative unless
`α = β = γ = π/2`, and then `P₄ = P₀`. Also `S > π` follows from the turn sum, because the two endpoint turns
cannot both vanish.
-/

open Real

namespace UnitHexagon

/-- The endpoint `P₄` of the chain. -/
noncomputable def P4x (α β γ : ℝ) : ℝ :=
  1 - Real.cos α + Real.cos (α + β) - Real.cos (α + β + γ)
noncomputable def P4y (α β γ : ℝ) : ℝ :=
  Real.sin α - Real.sin (α + β) + Real.sin (α + β + γ)

/-- The edge directions `0, π - α, 2π - α - β, 3π - S` give the edge vectors used above. -/
lemma edge_vectors (α β γ : ℝ) :
    (Real.cos (π - α), Real.sin (π - α)) = (-Real.cos α, Real.sin α) ∧
    (Real.cos (2 * π - (α + β)), Real.sin (2 * π - (α + β))) =
      (Real.cos (α + β), -Real.sin (α + β)) ∧
    (Real.cos (3 * π - (α + β + γ)), Real.sin (3 * π - (α + β + γ))) =
      (-Real.cos (α + β + γ), Real.sin (α + β + γ)) := by
  refine ⟨by simp [Real.cos_pi_sub, Real.sin_pi_sub], by simp [Real.cos_two_pi_sub, Real.sin_two_pi_sub], ?_⟩
  have h : 3 * π - (α + β + γ) = (π - (α + β + γ)) + 2 * π := by ring
  rw [h, Real.cos_add_two_pi, Real.sin_add_two_pi, Real.cos_pi_sub, Real.sin_pi_sub]

/-- Cross product at `P₄` of the incoming edge `(-cos S, sin S)` and the closing chord `P₀ - P₄`. -/
lemma cross_at_P4 (α β γ : ℝ) :
    (-Real.cos (α + β + γ)) * (-P4y α β γ) - Real.sin (α + β + γ) * (-P4x α β γ) =
      Real.sin γ - Real.sin (β + γ) + Real.sin (α + β + γ) := by
  set S := α + β + γ
  have e1 : Real.sin (α - S) = Real.sin α * Real.cos S - Real.cos α * Real.sin S := Real.sin_sub _ _
  have e2 : Real.sin (α + β - S) = Real.sin (α + β) * Real.cos S - Real.cos (α + β) * Real.sin S :=
    Real.sin_sub _ _
  have r1 : α - S = -(β + γ) := by simp only [S]; ring
  have r2 : α + β - S = -γ := by simp only [S]; ring
  rw [r1, Real.sin_neg] at e1
  rw [r2, Real.sin_neg] at e2
  unfold P4x P4y
  linear_combination (-1 : ℝ) * e1 + e2

/-- Cross product at `P₀` of the closing chord `P₀ - P₄` and the first edge `(1,0)`. -/
lemma cross_at_P0 (α β γ : ℝ) : (-P4x α β γ) * 0 - (-P4y α β γ) * 1 =
    Real.sin α - Real.sin (α + β) + Real.sin (α + β + γ) := by
  unfold P4y; ring

/-- The factorisation used in the second case of the proof. -/
lemma factor (β γ : ℝ) :
    Real.sin γ - Real.sin (β + γ) + Real.sin (2 * γ + β) =
      4 * Real.sin (γ / 2) * Real.cos ((β + γ) / 2) * Real.cos (γ + β / 2) := by
  have h1 : 2 * Real.cos ((β + γ) / 2) * Real.cos (γ + β / 2) =
      Real.cos (γ / 2) + Real.cos (3 * γ / 2 + β) := by
    rw [Real.two_mul_cos_mul_cos, show (β + γ) / 2 - (γ + β / 2) = -(γ / 2) by ring, Real.cos_neg,
      show (β + γ) / 2 + (γ + β / 2) = 3 * γ / 2 + β by ring]
  have h2 : 2 * Real.sin (γ / 2) * Real.cos (γ / 2) = Real.sin γ := by
    rw [Real.two_mul_sin_mul_cos, sub_self, Real.sin_zero, zero_add]; ring_nf
  have h3 : 2 * Real.sin (γ / 2) * Real.cos (3 * γ / 2 + β) =
      Real.sin (2 * γ + β) - Real.sin (β + γ) := by
    rw [Real.two_mul_sin_mul_cos, show γ / 2 - (3 * γ / 2 + β) = -(β + γ) by ring, Real.sin_neg,
      show γ / 2 + (3 * γ / 2 + β) = 2 * γ + β by ring]; ring
  linear_combination (-(2 : ℝ) * Real.sin (γ / 2)) * h1 - h2 - h3

lemma sin_neg_of_pi_lt {x : ℝ} (h1 : π < x) (h2 : x < 2 * π) : Real.sin x < 0 := by
  have := Real.sin_pos_of_pos_of_lt_pi (x := x - π) (by linarith) (by linarith)
  rw [Real.sin_sub_pi] at this; linarith

/-- The core estimate: with `γ ≤ α` and `S > π`, the cross product at `P₄` is negative,
except in the square case. -/
theorem K_neg {α β γ : ℝ} (ha : 0 < α) (hb : 0 < β) (hc : 0 < γ) (ha' : α ≤ π / 2)
    (hb' : β ≤ π / 2) (hc' : γ ≤ π / 2) (hS : π < α + β + γ) (hca : γ ≤ α) :
    Real.sin γ - Real.sin (β + γ) + Real.sin (α + β + γ) < 0 ∨
      (α = π / 2 ∧ β = π / 2 ∧ γ = π / 2) := by
  have hsS := sin_neg_of_pi_lt hS (by linarith [Real.pi_pos])
  rcases le_or_gt (2 * γ + β) π with hcase | hcase
  · left
    have := sin_le_sin_add hc.le hb.le hcase
    rw [add_comm γ β] at this
    linarith
  · -- sine is decreasing on [π, 3π/2], and 2γ + β ≤ S
    have hmono : Real.sin (α + β + γ) ≤ Real.sin (2 * γ + β) := by
      have := Real.sin_le_sin_of_le_of_le_pi_div_two (x := 2 * γ + β - π) (y := α + β + γ - π)
        (by linarith) (by linarith) (by linarith)
      rw [Real.sin_sub_pi, Real.sin_sub_pi] at this; linarith
    have hs : 0 < Real.sin (γ / 2) := Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
    have hcn : Real.cos (γ + β / 2) < 0 :=
      Real.cos_neg_of_pi_div_two_lt_of_lt (by linarith) (by linarith)
    rcases lt_or_eq_of_le (show β + γ ≤ π by linarith) with hlt | heq
    · left
      have hcp : 0 < Real.cos ((β + γ) / 2) :=
        Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
      have hf := factor β γ
      have : 4 * Real.sin (γ / 2) * Real.cos ((β + γ) / 2) * Real.cos (γ + β / 2) < 0 := by
        have := mul_pos hs hcp
        nlinarith
      linarith
    · right
      refine ⟨by linarith, by linarith, by linarith⟩

/-- Lemma 2.3: convexity at both endpoints with `S > π` forces the square case. -/
theorem four_hull {α β γ : ℝ} (ha : 0 < α) (hb : 0 < β) (hc : 0 < γ) (ha' : α ≤ π / 2)
    (hb' : β ≤ π / 2) (hc' : γ ≤ π / 2) (hS : π < α + β + γ)
    (hP0 : 0 ≤ (-P4x α β γ) * 0 - (-P4y α β γ) * 1)
    (hP4 : 0 ≤ (-Real.cos (α + β + γ)) * (-P4y α β γ) - Real.sin (α + β + γ) * (-P4x α β γ)) :
    α = π / 2 ∧ β = π / 2 ∧ γ = π / 2 := by
  rw [cross_at_P0] at hP0
  rw [cross_at_P4] at hP4
  rcases le_total γ α with h | h
  · rcases K_neg ha hb hc ha' hb' hc' hS h with hK | hsq
    · linarith
    · exact hsq
  · have hS' : π < γ + β + α := by linarith
    rcases K_neg hc hb ha hc' hb' ha' hS' h with hK | ⟨h1, h2, h3⟩
    · rw [show γ + β + α = α + β + γ by ring, add_comm β α] at hK; linarith
    · exact ⟨h3, h2, h1⟩

/-- In the square case the chain closes up: `P₄ = P₀`, contradicting distinctness. -/
lemma square_case_closes : P4x (π / 2) (π / 2) (π / 2) = 0 ∧ P4y (π / 2) (π / 2) (π / 2) = 0 := by
  unfold P4x P4y
  have h3 : π / 2 + π / 2 + π / 2 = π / 2 + π := by ring
  rw [h3, show π / 2 + π / 2 = π by ring]
  simp [Real.cos_add_pi, Real.sin_add_pi]

/-- With distinct `P₀, P₄`, four consecutive unit hull edges with middle angles in `(0, π/2]` and
`S > π` are impossible. -/
theorem no_four_unit_hull_edges {α β γ : ℝ} (ha : 0 < α) (hb : 0 < β) (hc : 0 < γ)
    (ha' : α ≤ π / 2) (hb' : β ≤ π / 2) (hc' : γ ≤ π / 2) (hS : π < α + β + γ)
    (hdist : (P4x α β γ, P4y α β γ) ≠ (0, 0))
    (hP0 : 0 ≤ (-P4x α β γ) * 0 - (-P4y α β γ) * 1)
    (hP4 : 0 ≤ (-Real.cos (α + β + γ)) * (-P4y α β γ) - Real.sin (α + β + γ) * (-P4x α β γ)) :
    False := by
  obtain ⟨rfl, rfl, rfl⟩ := four_hull ha hb hc ha' hb' hc' hS hP0 hP4
  obtain ⟨h1, h2⟩ := square_case_closes
  exact hdist (by rw [h1, h2])

/-- The turn sum gives `S > π`: the three middle turns `π - α, π - β, π - γ` and the endpoint turns
`t₀, t₄ ≥ 0` sum to `2π`, and the endpoint turns do not both vanish. -/
lemma S_gt_pi {α β γ t₀ t₄ : ℝ} (hsum : (π - α) + (π - β) + (π - γ) + t₀ + t₄ = 2 * π)
    (h0 : 0 ≤ t₀) (h4 : 0 ≤ t₄) (hne : ¬ (t₀ = 0 ∧ t₄ = 0)) : π < α + β + γ := by
  by_contra hc
  push Not at hc
  exact hne ⟨by linarith, by linarith⟩

/-- Both endpoint turns cannot vanish: then `P₃, P₄, P₀, P₁` lie in this order on a line and
`|P₃P₁| = 2 + |P₄P₀| > 2`, although the path `P₃P₂P₁` has length two. -/
lemma endpoint_turns_not_both_straight {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [MetricSpace P] [NormedAddTorsor V P] {P₀ P₁ P₂ P₃ P₄ : P}
    (h01 : dist P₀ P₁ = 1) (h12 : dist P₁ P₂ = 1) (h23 : dist P₂ P₃ = 1) (h34 : dist P₃ P₄ = 1)
    (h40 : P₄ ≠ P₀) (hw1 : Wbtw ℝ P₃ P₄ P₀) (hw2 : Wbtw ℝ P₃ P₀ P₁) : False := by
  have d1 := hw1.dist_add_dist
  have d2 := hw2.dist_add_dist
  have hpos : 0 < dist P₄ P₀ := dist_pos.2 h40
  have tri := dist_triangle P₃ P₂ P₁
  rw [dist_comm P₃ P₂, h23, dist_comm P₂ P₁, h12] at tri
  linarith
