import Mathlib

/-!
# First variation: a non-affine regression lets a monotone transform raise correlation

Work in `L²` with centred variables: `x` = centred `U`, `y` = centred `V`, and `h` = centred `h(U)` where
`h = r - (affine projection of r)`, `r(u) = E[V | U = u]`. Then `⟪h, x⟫ = 0` (projection) and
`⟪h, y⟫ = E[h(U) r(U)] = ‖h‖² > 0` when `r` is not affine (tower property; not formalised). This file proves the
inner-product step: there is an explicit `ε₀ > 0` with `corr(x + ε h, y) > corr(x, y)` for every
`0 < ε ≤ ε₀`.
-/

namespace FrankCopula

open RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Correlation of two vectors. -/
noncomputable def corr (x y : E) : ℝ := ⟪x, y⟫ / (‖x‖ * ‖y‖)

theorem corr_increase (x y h : E) (hx : x ≠ 0) (hy : y ≠ 0) (hxy : 0 < ⟪x, y⟫) (hhx : ⟪h, x⟫ = 0)
    (hhy : 0 < ⟪h, y⟫) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ → corr x y < corr (x + ε • h) y := by
  set c := ⟪x, y⟫; set d := ⟪h, y⟫; set n := ‖x‖; set m := ‖h‖
  have n0 : 0 < n := norm_pos_iff.mpr hx
  have y0 : 0 < ‖y‖ := norm_pos_iff.mpr hy
  set ε₀ := c * d * n ^ 2 / (c ^ 2 * m ^ 2 + 1) with hε₀
  refine ⟨ε₀, by positivity, fun ε ε0 hεε => ?_⟩
  have hN : ‖x + ε • h‖ ^ 2 = n ^ 2 + ε ^ 2 * m ^ 2 := by
    rw [@norm_add_sq_real, inner_smul_right, real_inner_comm, hhx, norm_smul, Real.norm_eq_abs,
      abs_of_pos ε0]; ring
  have N0 : 0 < ‖x + ε • h‖ := by
    have h2 : 0 < ‖x + ε • h‖ ^ 2 := by rw [hN]; positivity
    rcases (norm_nonneg (x + ε • h)).lt_or_eq with h1 | h1
    · exact h1
    · rw [← h1] at h2; simp at h2
  have hin : ⟪x + ε • h, y⟫ = c + ε * d := by rw [inner_add_left, inner_smul_left]; simp [c, d]
  unfold corr
  rw [hin, div_lt_div_iff₀ (by positivity) (by positivity)]
  -- c * (N * ‖y‖) < (c + ε d) * (n * ‖y‖)  ⟸  c N < (c + ε d) n, compare squares
  have key : c * ‖x + ε • h‖ < (c + ε * d) * n := by
    have hsq : (c * ‖x + ε • h‖) ^ 2 < ((c + ε * d) * n) ^ 2 := by
      rw [mul_pow, hN, mul_pow]
      have hm : ε * (c ^ 2 * m ^ 2) < c * d * n ^ 2 := by
        have hp : 0 < c * d * n ^ 2 := by positivity
        have h0 : ε₀ * (c ^ 2 * m ^ 2) < c * d * n ^ 2 := by
          rw [hε₀, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]; nlinarith
        nlinarith [mul_le_mul_of_nonneg_right hεε (by positivity : (0 : ℝ) ≤ c ^ 2 * m ^ 2)]
      nlinarith [mul_pos ε0 (mul_pos hxy hhy), sq_nonneg (ε * d * n), mul_pos ε0 ε0]
    exact (pow_lt_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).mp hsq
  nlinarith [mul_lt_mul_of_pos_right key y0]

end FrankCopula
