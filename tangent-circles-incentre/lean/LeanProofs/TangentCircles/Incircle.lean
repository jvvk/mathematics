import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

/-!
# Tangent circles: the triangle of centres (Section 2 and the conclusion)

Circles of radii `a, b, c` touch in pairs; the centres form a triangle with sides
`b + c, c + a, a + b`.
* `tangent_length`: the tangent length from the first centre, `(AB + AC - BC)/2`, is `a`; so the
  incircle touches each side at the contact point of the two circles.
* With `ρ² (a + b + c) = a b c` (the inradius, by Heron) the half-angles are `α = arctan (ρ/a)`,
  `β = arctan (ρ/b)`, `γ = arctan (ρ/c)`, and `half_angles`: `α + β + γ = π/2` (the angle sum).
* `rho_lt`: `ρ < √(ab)`, so the incentre lies inside the support of the crossing law.
* `miss_side` and `conclusion`: each side misses the incentre with probability
  `1/2 - (α + β)/π = γ/π = C/(2π)`, and the three add up to `1/2`.
-/

open Real

namespace TangentCircles

lemma tangent_length (a b c : ℝ) : ((a + b) + (a + c) - (b + c)) / 2 = a := by ring

section
variable {a b c ρ : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hρ : 0 < ρ)
  (hheron : ρ ^ 2 * (a + b + c) = a * b * c)
include ha hb hc hρ hheron

/-- `ρ² < ab`. -/
lemma rho_sq_lt : ρ ^ 2 < a * b := by
  have : ρ ^ 2 * c < a * b * c := by nlinarith [mul_pos (pow_pos hρ 2) (add_pos ha hb)]
  exact lt_of_mul_lt_mul_right this hc.le

omit ha hb hc hheron in
lemma rho_lt_of_sq {x : ℝ} (hx : ρ ^ 2 < x) : ρ < Real.sqrt x :=
  Real.lt_sqrt hρ.le |>.2 hx

/-- The angle sum, in half-angles: `arctan (ρ/a) + arctan (ρ/b) + arctan (ρ/c) = π/2`. -/
theorem half_angles :
    Real.arctan (ρ / a) + Real.arctan (ρ / b) + Real.arctan (ρ / c) = π / 2 := by
  have hab : ρ / a * (ρ / b) < 1 := by
    rw [div_mul_div_comm, div_lt_one (by positivity), ← pow_two]; exact rho_sq_lt ha hb hc hρ hheron
  rw [Real.arctan_add hab]
  -- (ρ/a + ρ/b)/(1 - ρ²/(ab)) = (ρ/c)⁻¹
  have hkey : (ρ / a + ρ / b) / (1 - ρ / a * (ρ / b)) = (ρ / c)⁻¹ := by
    have hden : a * b - ρ ^ 2 ≠ 0 := by have := rho_sq_lt ha hb hc hρ hheron; linarith
    have e1 : (ρ / a + ρ / b) / (1 - ρ / a * (ρ / b)) = ρ * (a + b) / (a * b - ρ ^ 2) := by
      field_simp
      ring
    rw [e1, inv_div]
    rw [div_eq_div_iff hden hρ.ne']
    nlinarith [hheron]
  rw [hkey, Real.arctan_inv_of_pos (by positivity)]; ring

/-- The side through the first two circles misses `I` with probability `1/2 - (α + β)/π = γ/π`. -/
theorem miss_side :
    1 / 2 - (Real.arctan (ρ / a) + Real.arctan (ρ / b)) / π = Real.arctan (ρ / c) / π := by
  have := half_angles ha hb hc hρ hheron
  have hπ := Real.pi_pos
  field_simp
  linarith

/-- The conclusion: the three disjoint miss events have total probability `1/2`. -/
theorem conclusion :
    (1 / 2 - (Real.arctan (ρ / a) + Real.arctan (ρ / b)) / π) +
    (1 / 2 - (Real.arctan (ρ / b) + Real.arctan (ρ / c)) / π) +
    (1 / 2 - (Real.arctan (ρ / c) + Real.arctan (ρ / a)) / π) = 1 / 2 := by
  have := half_angles ha hb hc hρ hheron
  have hπ := Real.pi_pos
  field_simp
  linarith

end

/-- Expected number of vertices on the inner arcs: arcs of central angle `2α, 2β, 2γ` give
`(2α + 2β + 2γ)/(2π) = 1/2`, the same number. -/
theorem inner_arcs {α β γ : ℝ} (h : α + β + γ = π / 2) :
    2 * α / (2 * π) + 2 * β / (2 * π) + 2 * γ / (2 * π) = 1 / 2 := by
  have hπ := Real.pi_pos
  field_simp
  linarith

end TangentCircles
