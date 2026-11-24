import Mathlib

/-!
# The Frank regression function is not affine

For the Frank copula with parameter `t ≠ 0`, the regression `r_t(u) = E[V | U = u]` has the closed form
`R t u = 1 - w (x - a u) / (x (x - a))` with `w = e^{-tu}`, `x = w - 1`, `a = e^{-t} - 1`
(derived in `Regression.lean`). Evaluated at `u = 1/8, 1/4, 1/2` the three values are not collinear: with
`s = e^{-t/8}` the defect is `-s (s-1)^3 (s+1) P(s) / (4 Q(s))` with `P, Q > 0`, which vanishes only at `s = 1`.
So no affine function agrees with `R t` on `(0, 1)`.
-/

namespace FrankCopula

open Real

/-- Closed form of `E[V | U = u]` for the Frank copula with parameter `t`. -/
noncomputable def R (t u : ℝ) : ℝ :=
  1 - exp (-t * u) * ((exp (-t * u) - 1) - (exp (-t) - 1) * u) /
    ((exp (-t * u) - 1) * (exp (-t * u) - exp (-t)))

/-- `R` in terms of `s = e^{-t/8}` at `u = k/8`. -/
lemma R_eighth (t : ℝ) (k : ℕ) :
    R t (k / 8) = 1 - exp (-t / 8) ^ k * ((exp (-t / 8) ^ k - 1) - (exp (-t / 8) ^ 8 - 1) * (k / 8)) /
      ((exp (-t / 8) ^ k - 1) * (exp (-t / 8) ^ k - exp (-t / 8) ^ 8)) := by
  have hk : ∀ m : ℕ, exp (-t / 8) ^ m = exp (-t * (m / 8)) := fun m => by
    rw [← exp_nat_mul]; congr 1; ring
  rw [R, hk k, hk 8]; norm_num

/-- **Three-point defect.** -/
theorem defect (t : ℝ) (ht : t ≠ 0) :
    (R t (1 / 2) - R t (1 / 4)) - 2 * (R t (1 / 4) - R t (1 / 8)) ≠ 0 := by
  set s := exp (-t / 8) with hs
  have s0 : 0 < s := exp_pos _
  have s1 : s ≠ 1 := by
    intro h; apply ht; have := congrArg log h; rw [hs, log_exp, log_one] at this; linarith
  have e1 := R_eighth t 1; have e2 := R_eighth t 2; have e4 := R_eighth t 4
  norm_num at e1 e2 e4
  rw [e1, e2, e4, ← hs]
  have p1 : s - 1 ≠ 0 := sub_ne_zero.mpr s1
  have pos : ∀ n : ℕ, 0 < n → s ^ n - 1 ≠ 0 := fun n hn h => s1 ((pow_eq_one_iff_of_nonneg s0.le hn.ne').mp
    (sub_eq_zero.mp h))
  have neg : ∀ n : ℕ, n < 8 → s ^ n - s ^ 8 ≠ 0 := by
    intro n hn h
    have : s ^ n = s ^ n * s ^ (8 - n) := by
      rw [← pow_add, Nat.add_sub_cancel' hn.le]; exact sub_eq_zero.mp h
    have h1 : s ^ (8 - n) = 1 := by
      have := (mul_right_eq_self₀).mp this.symm; simpa [(pow_pos s0 n).ne'] using this
    exact s1 ((pow_eq_one_iff_of_nonneg s0.le (by omega)).mp h1)
  have d1 := pos 1 one_pos; have d2 := pos 2 two_pos; have d4 := pos 4 (by norm_num)
  have n1 := neg 1 (by norm_num); have n2 := neg 2 (by norm_num); have n4 := neg 4 (by norm_num)
  simp only [pow_one] at d1 n1
  have key : (1 - s ^ 4 * (s ^ 4 - 1 - (s ^ 8 - 1) * (1 / 2)) / ((s ^ 4 - 1) * (s ^ 4 - s ^ 8)) -
        (1 - s ^ 2 * (s ^ 2 - 1 - (s ^ 8 - 1) * (1 / 4)) / ((s ^ 2 - 1) * (s ^ 2 - s ^ 8)))) -
      2 * ((1 - s ^ 2 * (s ^ 2 - 1 - (s ^ 8 - 1) * (1 / 4)) / ((s ^ 2 - 1) * (s ^ 2 - s ^ 8))) -
        (1 - s * (s - 1 - (s ^ 8 - 1) * (1 / 8)) / ((s - 1) * (s - s ^ 8)))) =
      -s * (s - 1) ^ 3 * (s + 1) * (s ^ 4 + s ^ 3 + 3 * s ^ 2 + s + 1) /
        (4 * ((s ^ 2 - s + 1) * (s ^ 2 + s + 1) * (s ^ 6 + s ^ 5 + s ^ 4 + s ^ 3 + s ^ 2 + s + 1))) := by
    have q1 : s ^ 2 - s + 1 ≠ 0 := by nlinarith [sq_nonneg (s - 1)]
    have q2 : s ^ 2 + s + 1 ≠ 0 := by positivity
    have q3 : s ^ 6 + s ^ 5 + s ^ 4 + s ^ 3 + s ^ 2 + s + 1 ≠ 0 := by positivity
    have r4 : 1 - s ^ 4 ≠ 0 := fun h => d4 (by linarith)
    have r6 : 1 - s ^ 6 ≠ 0 := fun h => pos 6 (by norm_num) (by linarith)
    have r7 : 1 - s ^ 7 ≠ 0 := fun h => pos 7 (by norm_num) (by linarith)
    have r0 : s * (s - 1) + 1 ≠ 0 := by nlinarith [sq_nonneg (s - 1)]
    field_simp
    ring
  rw [key]
  have q1 : 0 < s ^ 2 - s + 1 := by nlinarith [sq_nonneg (s - 1)]
  refine div_ne_zero ?_ (by positivity)
  refine mul_ne_zero (mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr s0.ne') (pow_ne_zero 3 p1)) (by positivity))
    (by positivity)

/-- **The Frank regression is not affine** on `(0, 1)`, for every `t ≠ 0`. -/
theorem not_affine (t : ℝ) (ht : t ≠ 0) :
    ¬ ∃ α β : ℝ, ∀ u ∈ Set.Ioo (0 : ℝ) 1, R t u = α + β * u := by
  rintro ⟨α, β, h⟩
  apply defect t ht
  rw [h _ ⟨by norm_num, by norm_num⟩, h _ ⟨by norm_num, by norm_num⟩, h _ ⟨by norm_num, by norm_num⟩]
  ring

end FrankCopula
