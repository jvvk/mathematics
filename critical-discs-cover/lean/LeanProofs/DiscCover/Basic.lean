import Mathlib

/-!
# Critical random discs cover the disc (MO 458793): the analytic core

The proof is conditional on Zhou's exact criterion for random ball coverings of tori
(arXiv:2609.02156) for the interior, and uses Shepp's theorem for the rim. This file checks the
estimates that feed the criteria.

* `lens_ball`: two unit balls whose centres are at distance `s ≤ 2` contain, in their
  intersection, the ball of radius `1 - s/2` about the midpoint; so the lens has area at least
  `π(1 - s/2)² ≥ π(1 - s)` (`lens_sq`).
* `sum_lower`: `Σ_{n ≤ N} (1/n)(1 - t√(πn)) ≥ 2 log(1/t) - log π - 2` for `N = ⌊1/(πt²)⌋`,
  the lower bound for Zhou's function `H`.
* `inv_not_integrable`: `t ↦ 1/t` is not integrable on `[0, 1]`, so `∫ e^H` diverges.
* `sliver`: `1 - √(1 - x²) ≤ x²` for `|x| ≤ 1`, the sliver estimate at the rim.
-/

namespace DiscCover

open Real Finset

/-- The ball of radius `1 - ‖z‖/2` about `z/2` lies in both unit balls `B(0, 1)` and `B(z, 1)`. -/
theorem lens_ball {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (z : E) :
    Metric.ball ((1 / 2 : ℝ) • z) (1 - ‖z‖ / 2) ⊆ Metric.ball 0 1 ∩ Metric.ball z 1 := by
  intro y hy
  rw [Metric.mem_ball] at hy
  have hz : ‖(1 / 2 : ℝ) • z‖ = ‖z‖ / 2 := by rw [norm_smul]; norm_num; ring
  refine ⟨?_, ?_⟩
  · rw [Metric.mem_ball, dist_zero_right]
    calc ‖y‖ = ‖(y - (1 / 2 : ℝ) • z) + (1 / 2 : ℝ) • z‖ := by rw [sub_add_cancel]
      _ ≤ ‖y - (1 / 2 : ℝ) • z‖ + ‖(1 / 2 : ℝ) • z‖ := norm_add_le _ _
      _ < 1 := by rw [hz, ← dist_eq_norm]; linarith
  · rw [Metric.mem_ball, dist_eq_norm]
    have : y - z = (y - (1 / 2 : ℝ) • z) - (1 / 2 : ℝ) • z := by
      rw [sub_sub, ← add_smul]; norm_num
    calc ‖y - z‖ = ‖(y - (1 / 2 : ℝ) • z) - (1 / 2 : ℝ) • z‖ := by rw [this]
      _ ≤ ‖y - (1 / 2 : ℝ) • z‖ + ‖(1 / 2 : ℝ) • z‖ := norm_sub_le _ _
      _ < 1 := by rw [hz, ← dist_eq_norm]; linarith

/-- `(1 - s/2)² ≥ 1 - s`: the lens function satisfies `ψ(s) ≥ 1 - s`. -/
theorem lens_sq (s : ℝ) : 1 - s ≤ (1 - s / 2) ^ 2 := by nlinarith [sq_nonneg s]

/-- `Σ_{n=1}^N 1/√n ≤ 2√N`. -/
theorem sum_inv_sqrt (N : ℕ) : ∑ n ∈ Icc 1 N, 1 / √(n : ℝ) ≤ 2 * √(N : ℝ) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sum_Icc_succ_top (by omega), Nat.cast_succ]
    have h1 : (0 : ℝ) < √((N : ℝ) + 1) := sqrt_pos.2 (by positivity)
    have h2 : √(N : ℝ) ≤ √((N : ℝ) + 1) := sqrt_le_sqrt (by linarith)
    have hsq : √((N : ℝ) + 1) ^ 2 = (N : ℝ) + 1 := sq_sqrt (by positivity)
    have hsq' : √(N : ℝ) ^ 2 = (N : ℝ) := sq_sqrt (by positivity)
    have key : 1 / √((N : ℝ) + 1) ≤ 2 * (√((N : ℝ) + 1) - √(N : ℝ)) := by
      rw [div_le_iff₀ h1]
      nlinarith [sqrt_nonneg (N : ℝ)]
    linarith

/-- `log (N + 1) ≤ Σ_{n=1}^N 1/n`. -/
theorem log_le_sum_inv (N : ℕ) : log ((N : ℝ) + 1) ≤ ∑ n ∈ Icc 1 N, 1 / (n : ℝ) := by
  have h := log_add_one_le_harmonic N
  rw [harmonic_eq_sum_Icc] at h
  push_cast at h
  simpa [one_div] using h

/-- The lower bound for Zhou's function: with `N = ⌊1/(πt²)⌋`,
`Σ_{n ≤ N} (1/n)(1 - t√(πn)) ≥ 2 log(1/t) - log π - 2`. -/
theorem sum_lower (t : ℝ) (ht : 0 < t) :
    2 * log (1 / t) - log π - 2 ≤
      ∑ n ∈ Icc 1 ⌊1 / (π * t ^ 2)⌋₊, (1 / (n : ℝ)) * (1 - t * √(π * n)) := by
  set N := ⌊1 / (π * t ^ 2)⌋₊
  have hx : 0 < 1 / (π * t ^ 2) := by positivity
  have hN1 : 1 / (π * t ^ 2) < (N : ℝ) + 1 := Nat.lt_floor_add_one _
  have hN0 : (N : ℝ) ≤ 1 / (π * t ^ 2) := Nat.floor_le hx.le
  -- split the sum
  have split : ∑ n ∈ Icc 1 N, (1 / (n : ℝ)) * (1 - t * √(π * n)) =
      ∑ n ∈ Icc 1 N, 1 / (n : ℝ) - t * √π * ∑ n ∈ Icc 1 N, 1 / √(n : ℝ) := by
    rw [mul_sum, ← sum_sub_distrib]
    refine sum_congr rfl fun n hn => ?_
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (mem_Icc.1 hn).1
    have hsn : √(n : ℝ) ^ 2 = n := sq_sqrt (by linarith)
    have hpos : 0 < √(n : ℝ) := sqrt_pos.2 (by linarith)
    rw [sqrt_mul pi_pos.le]
    field_simp
    linear_combination (-t * √π) * hsn
  rw [split]
  -- the harmonic part
  have hlog : 2 * log (1 / t) - log π ≤ log ((N : ℝ) + 1) := by
    have : 2 * log (1 / t) - log π = log (1 / (π * t ^ 2)) := by
      rw [one_div (π * t ^ 2), log_inv, log_mul pi_pos.ne' (pow_ne_zero 2 ht.ne'), log_pow,
        one_div t, log_inv]
      push_cast; ring
    rw [this]
    exact log_le_log hx hN1.le
  -- the correction: t √π · 2√N ≤ 2
  have hcorr : t * √π * ∑ n ∈ Icc 1 N, 1 / √(n : ℝ) ≤ 2 := by
    have hs := sum_inv_sqrt N
    have hroot : t * √π * √(N : ℝ) ≤ 1 := by
      have : (t * √π * √(N : ℝ)) ^ 2 ≤ 1 := by
        rw [mul_pow, mul_pow, sq_sqrt pi_pos.le, sq_sqrt (Nat.cast_nonneg N)]
        calc t ^ 2 * π * (N : ℝ) ≤ t ^ 2 * π * (1 / (π * t ^ 2)) :=
              mul_le_mul_of_nonneg_left hN0 (by positivity)
          _ = 1 := by field_simp
      nlinarith [sq_nonneg (t * √π * √(N : ℝ)), mul_nonneg (mul_nonneg ht.le (sqrt_nonneg π))
        (sqrt_nonneg (N : ℝ))]
    have hc : 0 ≤ t * √π := by positivity
    calc t * √π * ∑ n ∈ Icc 1 N, 1 / √(n : ℝ) ≤ t * √π * (2 * √(N : ℝ)) :=
          mul_le_mul_of_nonneg_left hs hc
      _ = 2 * (t * √π * √(N : ℝ)) := by ring
      _ ≤ 2 := by linarith
  linarith [log_le_sum_inv N]

/-- `t ↦ t⁻¹` is not interval integrable on `[0, 1]`: so `∫ e^H dm ≥ c ∫₀ t⁻² · 2πt dt = ∞`. -/
theorem inv_not_integrable : ¬ IntervalIntegrable (fun t : ℝ => t⁻¹) MeasureTheory.volume 0 1 := by
  rw [intervalIntegrable_inv_iff]
  push Not
  refine ⟨by norm_num, ?_⟩
  simp

/-- The sliver estimate at the rim: `1 - √(1 - x²) ≤ x²` for `|x| ≤ 1`. -/
theorem sliver (x : ℝ) (hx : |x| ≤ 1) : 1 - √(1 - x ^ 2) ≤ x ^ 2 := by
  have h0 : 0 ≤ 1 - x ^ 2 := by nlinarith [sq_abs x, abs_nonneg x]
  have h1 : 1 - x ^ 2 ≤ √(1 - x ^ 2) := by
    have := sqrt_le_sqrt (show (1 - x ^ 2) ^ 2 ≤ 1 - x ^ 2 by nlinarith [sq_nonneg x])
    rwa [sqrt_sq h0] at this
  linarith

end DiscCover
