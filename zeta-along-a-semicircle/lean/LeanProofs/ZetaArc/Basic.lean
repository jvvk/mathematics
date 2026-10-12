import Mathlib

/-!
# |ζ| along a semicircle (MSE 5150160): the reductions

The proof that `|ζ(1 - r e^{iu})|` increases on `[0, π]` (for `r = 3, 5`) is computer assisted: ball
arithmetic encloses `R(u) = Re(z'(u) ζ'/ζ(z(u)))` on boxes. This file checks the exact reductions
that turn those
enclosures into a proof.

* `re_ratio`: with `z = 1 - r e^{iu}` and `z₀ = 1 - r`, `Re(z'/(z - z₀)) = (1/2) cot(u/2)`.
* `log_deriv_split`: `((z - z₀) h)'/((z - z₀) h) = 1/(z - z₀) + h'/h`.
* `region_a`: if `(1/2) cot(u/2) > r M` and `|h'/h| ≤ M`, then `Re(z' (1/(z - z₀) + h'/h)) > 0`.
* `R_pi`: at `u = π`, `z' = r i` and `ζ, ζ'` are real at `1 + r`, so `R(π) = 0`.
* `pos_of_deriv_neg`: if `R' < 0` on `(a, π)` and `R(π) = 0`, then `R > 0` on `[a, π)`.
-/

namespace ZetaArc

open Complex

/-- `Re(z'/(z - z₀)) = (1/2) cot(u/2)` for `z(u) = 1 - r e^{iu}`, `z₀ = 1 - r`. -/
theorem re_ratio (r u : ℝ) (hr : r ≠ 0) (hu : Real.sin (u / 2) ≠ 0) :
    ((-(r : ℂ) * I * exp (u * I)) / ((1 - r * exp (u * I)) - (1 - r))).re =
      Real.cos (u / 2) / (2 * Real.sin (u / 2)) := by
  have hc : Real.cos u = 1 - 2 * Real.sin (u / 2) ^ 2 := by
    rw [show u = 2 * (u / 2) by ring, Real.cos_two_mul, Real.cos_sq']; ring_nf
  have hs : Real.sin u = 2 * Real.sin (u / 2) * Real.cos (u / 2) := by
    rw [show u = 2 * (u / 2) by ring, Real.sin_two_mul]; ring_nf
  set sn := Real.sin (u / 2)
  set cs := Real.cos (u / 2)
  have hne : (1 : ℂ) - exp (u * I) ≠ 0 := by
    intro h
    have h' := congrArg Complex.re h
    simp only [sub_re, one_re, exp_ofReal_mul_I_re, zero_re] at h'
    have : sn ^ 2 = 0 := by linarith
    exact hu (pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this)
  have e : (-(r : ℂ) * I * exp (u * I)) / ((1 - r * exp (u * I)) - (1 - r)) =
      (-I * exp (u * I)) / (1 - exp (u * I)) := by
    have h1 : (1 - (r : ℂ) * exp (u * I)) - (1 - r) = r * (1 - exp (u * I)) := by ring
    have hr' : (r : ℂ) ≠ 0 := by exact_mod_cast hr
    rw [h1]; field_simp
  rw [e, exp_mul_I, ← ofReal_cos, ← ofReal_sin, div_re]
  simp only [mul_re, mul_im, neg_re, neg_im, I_re, I_im, ofReal_re, ofReal_im, sub_re, sub_im,
    one_re, one_im, add_re, add_im, normSq_apply]
  rw [hc, hs, ← add_div]
  have hsq : sn ^ 2 + cs ^ 2 = 1 := Real.sin_sq_add_cos_sq _
  have hs2 : 0 < sn ^ 2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hu))
  rw [div_eq_div_iff (by nlinarith [pow_pos hs2 2, sq_nonneg (sn * cs)])
    (mul_ne_zero two_ne_zero hu)]
  linear_combination (-4 * sn ^ 2 * cs) * hsq

/-- The logarithmic derivative of `(z - z₀) h` splits as `1/(z - z₀) + h'/h`. -/
theorem log_deriv_split (z z₀ h h' : ℂ) (hz : z - z₀ ≠ 0) (hh : h ≠ 0) :
    (h + (z - z₀) * h') / ((z - z₀) * h) = 1 / (z - z₀) + h' / h := by
  field_simp

/-- Region A: if `(1/2) cot(u/2) > r M` and `|h'/h| ≤ M`, then `R > 0`. -/
theorem region_a (zp q k : ℂ) (r M c : ℝ) (hre : (zp * q).re = c) (hzp : ‖zp‖ = r)
    (hk : ‖k‖ ≤ M)
    (hr : 0 ≤ r) (hgap : r * M < c) : 0 < (zp * (q + k)).re := by
  rw [mul_add, add_re, hre]
  have : |(zp * k).re| ≤ r * M := by
    calc |(zp * k).re| ≤ ‖zp * k‖ := abs_re_le_norm _
      _ = ‖zp‖ * ‖k‖ := norm_mul _ _
      _ ≤ r * M := by rw [hzp]; exact mul_le_mul_of_nonneg_left hk hr
  linarith [neg_abs_le (zp * k).re]

/-- At `u = π`: `z' = -r i e^{iπ} = r i`, and `R(π) = Re(r i ζ'(1 + r)/ζ(1 + r)) = 0` for real
values. -/
theorem R_pi (r a b : ℝ) :
    ((-(r : ℂ) * I * exp (Real.pi * I)) * ((a : ℂ) / b)).re = 0 := by
  rw [exp_pi_mul_I]
  simp [mul_re, div_re, div_im]

/-- Near `π`: `R' < 0` on `(a, π)` and `R(π) = 0` give `R > 0` on `[a, π)`. -/
theorem pos_of_deriv_neg (R : ℝ → ℝ) (a : ℝ) (hc : ContinuousOn R (Set.Icc a Real.pi))
    (hd : ∀ x ∈ Set.Ioo a Real.pi, HasDerivAt R (deriv R x) x ∧ deriv R x < 0)
    (h0 : R Real.pi = 0) : ∀ x ∈ Set.Ico a Real.pi, 0 < R x := by
  have hanti : StrictAntiOn R (Set.Icc a Real.pi) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc a Real.pi) hc
    intro x hx
    rw [interior_Icc] at hx
    exact (hd x hx).2
  intro x hx
  have := hanti ⟨hx.1, hx.2.le⟩ ⟨hx.1.trans hx.2.le, le_rfl⟩ hx.2
  linarith

end ZetaArc
