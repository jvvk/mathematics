import Mathlib

/-!
# Coins in a tray (MO 513668): the rim angles

Two coins of radii `1/j`, `1/k` touching the unit tray and each other have centres at distances
`1 - 1/j`, `1 - 1/k` from the centre and `1/j + 1/k` apart; by the law of cosines the angle
`α_d` they subtend at the centre has `cos α_d = 1 - 2/d` with `d = (j - 1)(k - 1)`.
* `rim_cos`: the law-of-cosines identity;
* `alpha_rat_iff`: `α_d` is a rational multiple of `π` iff `d ∈ {1, 2, 4}` (Niven);
* `alpha_irrational_n5`: so `α_6, α_8, α_12, α_16` are not (the pairs `(1/3,1/4)`, `(1/3,1/5)`,
  `(1/4,1/5)`, `(1/5,1/5)` in the `n = 5` argument);
* `dan_four`: `2 α_3 + α_9 = π` (the asker's `n = 4` ring `1/3, 1/2, 1/4, 1/4, 1/2`);
* `halves_overlap`: two coins of radius `1/2` touching the tray, `120°` apart, overlap;
* `root_unique`: the only Apollonian root quadruple `(-1, b, c, d)` is `(-1, 2, 2, 3)`.
-/

open Real

namespace CoinsTray

/-- The angle at the centre of the tray between two touching rim coins with `d = (j-1)(k-1)`. -/
noncomputable def alpha (d : ℝ) : ℝ := arccos (1 - 2 / d)

/-- The law of cosines for two touching rim coins. -/
theorem rim_cos (j k : ℝ) (hj : 1 < j) (hk : 1 < k) :
    ((1 - 1 / j) ^ 2 + (1 - 1 / k) ^ 2 - (1 / j + 1 / k) ^ 2) / (2 * (1 - 1 / j) * (1 - 1 / k)) =
      1 - 2 / ((j - 1) * (k - 1)) := by
  have hj0 : j ≠ 0 := by linarith
  have hk0 : k ≠ 0 := by linarith
  have hj1 : j - 1 ≠ 0 := by linarith
  have hk1 : k - 1 ≠ 0 := by linarith
  have h1 : 1 - 1 / j ≠ 0 := by rw [one_sub_div hj0]; exact div_ne_zero hj1 hj0
  have h2 : 1 - 1 / k ≠ 0 := by rw [one_sub_div hk0]; exact div_ne_zero hk1 hk0
  field_simp
  ring

lemma cos_alpha (d : ℝ) (hd : 1 ≤ d) : cos (alpha d) = 1 - 2 / d := by
  have h0 : 0 < d := by linarith
  apply cos_arccos
  · have : 2 / d ≤ 2 := by rw [div_le_iff₀ h0]; linarith
    linarith
  · have : 0 < 2 / d := by positivity
    linarith

/-- Niven: `α_d ∈ ℚ π` iff `d ∈ {1, 2, 4}` (for integers `d ≥ 1`). -/
theorem alpha_rat_iff (d : ℕ) (hd : 1 ≤ d) :
    (∃ r : ℚ, alpha d = r * π) ↔ d = 1 ∨ d = 2 ∨ d = 4 := by
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hd0 : (0 : ℝ) < d := by linarith
  constructor
  · intro hr
    have hc := niven hr ⟨1 - 2 / d, by rw [cos_alpha d hd']; push_cast; ring⟩
    rw [cos_alpha d hd'] at hc
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hc
    rcases hc with h | h | h | h | h
    · left; have : (d : ℝ) = 1 := by field_simp at h; linarith
      exact_mod_cast this
    · exfalso
      have : (d : ℝ) * 3 = 4 := by field_simp at h; linarith
      have : d * 3 = 4 := by exact_mod_cast this
      omega
    · right; left; have : (d : ℝ) = 2 := by field_simp at h; linarith
      exact_mod_cast this
    · right; right; have : (d : ℝ) = 4 := by field_simp at h; linarith
      exact_mod_cast this
    · exfalso; have : 2 / (d : ℝ) = 0 := by linarith
      exact absurd this (by positivity)
  · rintro (rfl | rfl | rfl)
    · refine ⟨1, ?_⟩; simp [alpha]; norm_num
    · refine ⟨1 / 2, ?_⟩; simp [alpha]; norm_num; ring
    · refine ⟨1 / 3, ?_⟩
      simp only [alpha]; norm_num
      rw [show (1 / 2 : ℝ) = cos (π / 3) by rw [cos_pi_div_three]]
      rw [arccos_cos (by positivity) (by linarith [pi_pos])]; ring

/-- The four pairs excluded by hand for `n = 5` have irrational angles. -/
theorem alpha_irrational_n5 (d : ℕ) (hd : d ∈ ({6, 8, 12, 16} : Finset ℕ)) :
    ¬ ∃ r : ℚ, alpha d = r * π := by
  rw [alpha_rat_iff d (by simp at hd; omega)]
  simp at hd; omega

/-- The asker's `n = 4` ring: `2 α_3 + α_9 = π`. -/
theorem dan_four : 2 * alpha 3 + alpha 9 = π := by
  have h3 : cos (alpha 3) = 1 / 3 := by rw [cos_alpha 3 (by norm_num)]; norm_num
  have h9 : cos (alpha 9) = 7 / 9 := by rw [cos_alpha 9 (by norm_num)]; norm_num
  have r3 : 0 ≤ alpha 3 ∧ alpha 3 ≤ π := ⟨arccos_nonneg _, arccos_le_pi _⟩
  -- `α_3 ≥ π/4` since `cos α_3 = 1/3 ≤ cos(π/4)`, so `π - 2 α_3 ∈ [0, π/2]`
  have hle : alpha 3 ≤ π / 2 := by
    rw [alpha, show π / 2 = arccos 0 by simp]
    exact arccos_le_arccos (by norm_num)
  have hge : π / 4 ≤ alpha 3 := by
    rw [alpha]; norm_num
    rw [show π / 4 = arccos (√2 / 2) by rw [← cos_pi_div_four, arccos_cos (by positivity)
      (by linarith [pi_pos])]]
    apply arccos_le_arccos
    have : (1 : ℝ) / 3 ≤ √2 / 2 := by
      rw [div_le_div_iff₀ (by norm_num) (by norm_num)]
      have : (1 : ℝ) ≤ √2 := by rw [show (1:ℝ) = √1 by simp]; exact sqrt_le_sqrt (by norm_num)
      linarith
    linarith
  have hc : cos (π - 2 * alpha 3) = 7 / 9 := by
    rw [cos_pi_sub, cos_two_mul, h3]; norm_num
  have : alpha 9 = π - 2 * alpha 3 := by
    rw [alpha, show (1 : ℝ) - 2 / 9 = 7 / 9 by norm_num, ← hc,
      arccos_cos (by linarith) (by linarith)]
  linarith

/-- Two coins of radius `1/2` touching the tray with centres `120°` apart overlap: their centres,
at distance `1/2` from the centre of the tray, are `√3/2 < 1` apart. -/
theorem halves_overlap :
    Real.sqrt ((1 / 2 - 1 / 2 * cos (2 * π / 3)) ^ 2 + (0 - 1 / 2 * sin (2 * π / 3)) ^ 2) <
      1 / 2 + 1 / 2 := by
  have hc : cos (2 * π / 3) = -1 / 2 := by
    rw [show 2 * π / 3 = π - π / 3 by ring, cos_pi_sub, cos_pi_div_three]; norm_num
  have hs : sin (2 * π / 3) = √3 / 2 := by
    rw [show 2 * π / 3 = π - π / 3 by ring, sin_pi_sub, sin_pi_div_three]
  rw [hc, hs]
  have h3 : √3 ^ 2 = 3 := sq_sqrt (by norm_num)
  rw [show (1 / 2 - 1 / 2 * (-1 / 2) : ℝ) ^ 2 + (0 - 1 / 2 * (√3 / 2)) ^ 2 = 3 / 4 by nlinarith]
  rw [show (1 / 2 + 1 / 2 : ℝ) = √1 by norm_num]
  exact sqrt_lt_sqrt (by norm_num) (by norm_num)

/-- A root quadruple `(-1, b, c, d)` (Graham et al.: `2 ≤ b ≤ c ≤ d ≤ -1 + b + c`, Descartes'
equation) is `(-1, 2, 2, 3)`. With `x = -1 + b + c`, Descartes gives `(x - d)² = 4(bc - b - c)`, and
`0 ≤ x - d ≤ b - 1`, `c ≥ b` force `4(b² - 2b) ≤ (b - 1)²`, so `b = 2`, then `c = 2`, `d = 3`. -/
theorem root_unique (b c d : ℤ) (h2 : 2 ≤ b) (hbc : b ≤ c) (hcd : c ≤ d) (hroot : d ≤ -1 + b + c)
    (hdes : (-1 + b + c + d) ^ 2 = 2 * (1 + b ^ 2 + c ^ 2 + d ^ 2)) :
    b = 2 ∧ c = 2 ∧ d = 3 := by
  have key : (-1 + b + c - d) ^ 2 = 4 * (b * c - b - c) := by linear_combination (-1 : ℤ) * hdes
  have hx0 : 0 ≤ -1 + b + c - d := by linarith
  have hx1 : -1 + b + c - d ≤ b - 1 := by linarith
  have hsq : (-1 + b + c - d) ^ 2 ≤ (b - 1) ^ 2 := pow_le_pow_left₀ hx0 hx1 2
  have hlow : b * (b - 1) ≤ c * (b - 1) := mul_le_mul_of_nonneg_right hbc (by linarith)
  have hb : b = 2 := by nlinarith
  subst hb
  have hc : c = 2 := by nlinarith
  subst hc
  have : (3 - d) ^ 2 = 0 := by linear_combination key
  have : 3 - d = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
  exact ⟨rfl, rfl, by linarith⟩

end CoinsTray
