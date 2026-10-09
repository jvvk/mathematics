import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

/-!
# Tangent circles: chord identities (Section 3)

Two circles of radii `a, b` touch at `T = (0,0)`, centres `(-a, 0)` and `(b, 0)`, common tangent the
`y`-axis. A line through `Z = (0, z)` with direction `(cos ω, sin ω)` has half-chords `c_A, c_B` and
chord midpoints at distances `m_A = a cos ω + z sin ω`, `m_B = b cos ω - z sin ω` from `Z`. With
`z cos p = a sin p` and `z cos q = b sin q`:
* `c_A² cos² p = a² cos ω cos (ω - 2p)` and `c_B² cos² q = b² cos ω cos (ω + 2q)`,
  where `c² = m² - z²`
  (the tangent is the radical axis, so `Z` has power `z²` for both circles);
* `m_A + m_B = (a + b) cos ω`;
* with `ω = (p - q) + η` and `s = p + q`: `cos (ω - 2p) cos (ω + 2q) = cos² s - sin² η`;
* the tidying identity `(a + b) cos p cos q cos (p - q) = b cos² p + a cos² q`, and
  `a / (a² + z²) = cos² p / a`.
-/

open Real

namespace TangentCircles

lemma halfchord_A {a z p ω : ℝ} (hz : z * Real.cos p = a * Real.sin p) :
    ((a * Real.cos ω + z * Real.sin ω) ^ 2 - z ^ 2) * Real.cos p ^ 2 =
      a ^ 2 * Real.cos ω * Real.cos (ω - 2 * p) := by
  have e : ((a * Real.cos ω + z * Real.sin ω) ^ 2 - z ^ 2) * Real.cos p ^ 2 =
      (a * Real.cos ω * Real.cos p + (z * Real.cos p) * Real.sin ω) ^ 2 - (z * Real.cos p) ^ 2 := by
    ring
  rw [e, hz, Real.cos_sub, Real.cos_two_mul, Real.sin_two_mul]
  linear_combination (a ^ 2 * Real.sin p ^ 2) * Real.sin_sq_add_cos_sq ω -
    (a ^ 2 * Real.cos ω ^ 2) * Real.sin_sq_add_cos_sq p

lemma halfchord_B {b z q ω : ℝ} (hz : z * Real.cos q = b * Real.sin q) :
    ((b * Real.cos ω - z * Real.sin ω) ^ 2 - z ^ 2) * Real.cos q ^ 2 =
      b ^ 2 * Real.cos ω * Real.cos (ω + 2 * q) := by
  have e : ((b * Real.cos ω - z * Real.sin ω) ^ 2 - z ^ 2) * Real.cos q ^ 2 =
      (b * Real.cos ω * Real.cos q - (z * Real.cos q) * Real.sin ω) ^ 2 - (z * Real.cos q) ^ 2 := by
    ring
  rw [e, hz, Real.cos_add, Real.cos_two_mul, Real.sin_two_mul]
  linear_combination (b ^ 2 * Real.sin q ^ 2) * Real.sin_sq_add_cos_sq ω -
    (b ^ 2 * Real.cos ω ^ 2) * Real.sin_sq_add_cos_sq q

lemma midpoints_sum (a b z ω : ℝ) :
    (a * Real.cos ω + z * Real.sin ω) + (b * Real.cos ω - z * Real.sin ω) =
      (a + b) * Real.cos ω := by
  ring

lemma product_identity (p q η : ℝ) :
    Real.cos ((p - q + η) - 2 * p) * Real.cos ((p - q + η) + 2 * q) =
      Real.cos (p + q) ^ 2 - Real.sin η ^ 2 := by
  have key : ∀ σ : ℝ, Real.cos (η - σ) * Real.cos (η + σ) = Real.cos σ ^ 2 - Real.sin η ^ 2 := by
    intro σ
    rw [Real.cos_sub η σ, Real.cos_add η σ]
    linear_combination (Real.cos σ ^ 2) * Real.sin_sq_add_cos_sq η -
      (Real.sin η ^ 2) * Real.sin_sq_add_cos_sq σ
  rw [show (p - q + η) - 2 * p = η - (p + q) by ring,
    show (p - q + η) + 2 * q = η + (p + q) by ring]
  exact key (p + q)

/-- The tidying identity: with `a sin p cos q = b sin q cos p` (both equal `z cos p cos q`). -/
lemma tidy {a b p q : ℝ} (h : a * Real.sin p * Real.cos q = b * Real.sin q * Real.cos p) :
    (a + b) * Real.cos p * Real.cos q * Real.cos (p - q) =
      b * Real.cos p ^ 2 + a * Real.cos q ^ 2 := by
  rw [Real.cos_sub]
  linear_combination (a * Real.cos q ^ 2) * Real.sin_sq_add_cos_sq p +
    (b * Real.cos p ^ 2) * Real.sin_sq_add_cos_sq q +
    (Real.sin q * Real.cos p - Real.sin p * Real.cos q) * h

lemma a_div {a z p : ℝ} (ha : a ≠ 0) (hc : Real.cos p ≠ 0) (hz : z * Real.cos p = a * Real.sin p) :
    a / (a ^ 2 + z ^ 2) = Real.cos p ^ 2 / a := by
  have hz' : z = a * Real.sin p / Real.cos p := by field_simp; linarith
  subst hz'
  have h1 : a ^ 2 + (a * Real.sin p / Real.cos p) ^ 2 = a ^ 2 / Real.cos p ^ 2 := by
    field_simp; linear_combination Real.sin_sq_add_cos_sq p
  rw [h1]; field_simp

end TangentCircles
