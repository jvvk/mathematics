import AlternatingSum.Coeffs
import Mathlib.Basic.Real.Basic

/-!
  Corollaries of Theorem 1: `L ≥ 0`, `L = 0` for odd `a`, `L > 0` exactly when `a` is even and
  `n ≥ a/2`, positivity of `G` for real `N ≥ 1`, and Abdesselam's extreme case `n = a + b`.
-/

namespace Abdesselam

open MvPowerSeries Finset Nat

/-- Nonnegative coefficients. -/
def NN (F : PS) : Prop := ∀ d, 0 ≤ coeff d F

theorem NN_mul {F G : PS} (hF : NN F) (hG : NN G) : NN (F * G) := by
  classical
  intro d; rw [coeff_mul]; exact sum_nonneg fun p _ ↦ mul_nonneg (hF _) (hG _)

theorem NN_one : NN 1 := by
  classical
  intro d; rw [coeff_one]; split_ifs <;> norm_num

theorem NN_pow {F : PS} (hF : NN F) (k : ℕ) : NN (F ^ k) := by
  induction k with
  | zero => rw [pow_zero]; exact NN_one
  | succ k ih => rw [pow_succ]; exact NN_mul ih hF

theorem coeff_R_pow' (m : ℕ) (d : Fin 2 →₀ ℕ) :
    coeff d (R ^ (m + 1)) =
      if Even (d 0) then ((m + d 0 / 2).choose m : ℚ) *
        ((2 * m + d 0 + 1 + d 1).choose (2 * m + d 0 + 1) : ℚ) else 0 := by
  rw [← coeff_R_pow, mono_self]

theorem NN_R_pow (m : ℕ) : NN (R ^ (m + 1)) := by
  intro d; rw [coeff_R_pow']; split_ifs
  · exact mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  · exact le_rfl

theorem coeff_R (d : Fin 2 →₀ ℕ) : coeff d R = coeff d (R ^ (0 + 1)) := by rw [zero_add, pow_one]

theorem coeff_R_sub_one (d : Fin 2 →₀ ℕ) :
    coeff d (R - 1) = if d = 0 then 0 else coeff d R := by
  classical
  rw [map_sub, coeff_one]
  split_ifs with h
  · subst h; rw [coeff_R, coeff_R_pow']; simp
  · rw [sub_zero]

theorem NN_R_sub_one : NN (R - 1) := by
  intro d; rw [coeff_R_sub_one]; split_ifs
  · exact le_refl 0
  · rw [coeff_R]; exact NN_R_pow 0 d

/-- **Corollary 2, first part:** `L ≥ 0`. -/
theorem L_nonneg (u a b n : ℕ) (hn : n ≤ a + b) : 0 ≤ L u a b n := by
  rw [main u a b n hn]
  exact mul_nonneg (by positivity) (NN_mul (NN_R_pow u) (NN_pow NN_R_sub_one _) _)

/-- Even in `w`: the coefficients at odd powers of `w` vanish. -/
def EvenW (F : PS) : Prop := ∀ d : Fin 2 →₀ ℕ, ¬ Even (d 0) → coeff d F = 0

theorem EvenW_mul {F G : PS} (hF : EvenW F) (hG : EvenW G) : EvenW (F * G) := by
  classical
  intro d hd; rw [coeff_mul]
  refine sum_eq_zero fun p hp ↦ ?_
  rw [mem_antidiagonal] at hp
  have h0 : p.1 0 + p.2 0 = d 0 := by simpa using congrArg (· 0) hp
  by_cases h1 : Even (p.1 0)
  · have h2 : ¬ Even (p.2 0) := fun h2 ↦ hd (h0 ▸ h1.add h2)
    rw [hG _ h2, mul_zero]
  · rw [hF _ h1, zero_mul]

theorem EvenW_one : EvenW 1 := by
  classical
  intro d hd; rw [coeff_one, ite_eq_right]; rintro rfl; exact hd (by simp)

theorem EvenW_pow {F : PS} (hF : EvenW F) (k : ℕ) : EvenW (F ^ k) := by
  induction k with
  | zero => rw [pow_zero]; exact EvenW_one
  | succ k ih => rw [pow_succ]; exact EvenW_mul ih hF

theorem EvenW_R_pow (m : ℕ) : EvenW (R ^ (m + 1)) := by
  intro d hd; rw [coeff_R_pow', ite_eq_right hd]

theorem EvenW_R_sub_one : EvenW (R - 1) := by
  intro d hd; rw [coeff_R_sub_one]; split_ifs
  · rfl
  · rw [coeff_R]; exact EvenW_R_pow 0 d hd

/-- **Corollary 2, second part:** `L = 0` for odd `a` (shown directly by Hucht on MO). -/
theorem L_odd (u a b n : ℕ) (hn : n ≤ a + b) (ha : ¬ Even a) : L u a b n = 0 := by
  rw [main u a b n hn, EvenW_mul (EvenW_R_pow u) (EvenW_pow EvenW_R_sub_one _) _ (by simpa using ha),
    mul_zero]

/-- **Corollary 5** (Abdesselam's extreme case `n = a + b`). -/
theorem L_extreme (u a b : ℕ) (ha : Even a) :
    L u a b (a + b) = (u ! : ℚ) ^ 2 * ((2 * u + a + b + 1).choose b : ℚ) *
      ((u + a / 2).choose (a / 2) : ℚ) := by
  rw [main u a b (a + b) le_rfl, Nat.sub_self, pow_zero, mul_one, coeff_R_pow, ite_eq_left ha]
  simp only [add_zero, factorial_zero, cast_one, div_one]
  have h1 : (u + a / 2).choose u = (u + a / 2).choose (a / 2) := Nat.choose_symm_add
  have h2 : (2 * u + a + 1 + b).choose (2 * u + a + 1) = (2 * u + a + b + 1).choose b := by
    rw [Nat.choose_symm_add, show 2 * u + a + 1 + b = 2 * u + a + b + 1 by ring]
  rw [h1, h2]
  ring

/-- The rising factorial `(x)_k = x (x+1) ⋯ (x+k-1)`. -/
def rising (x : ℝ) (k : ℕ) : ℝ := ∏ i ∈ range k, (x + i)

theorem rising_nonneg {x : ℝ} (hx : 0 ≤ x) (k : ℕ) : 0 ≤ rising x k :=
  prod_nonneg fun i _ ↦ by positivity

/-- Abdesselam's moment `G(u,a,b)` through the right side of identity (2), for real `N`. -/
noncomputable def Gmom (u a b : ℕ) (N : ℝ) : ℝ :=
  (a ! * b ! : ℝ) / rising N (u + a + b) ^ 2 *
    ∑ n ∈ range (a + b + 1), (L u a b n : ℝ) * rising (N - 1) n

/-- **Corollary 3:** `G(u,a,b) ≥ 0` for every real `N ≥ 1`. -/
theorem G_nonneg (u a b : ℕ) (N : ℝ) (hN : 1 ≤ N) : 0 ≤ Gmom u a b N := by
  unfold Gmom
  refine mul_nonneg (div_nonneg (by positivity) (sq_nonneg _)) (sum_nonneg fun n hn ↦ ?_)
  have hn := mem_range.1 hn
  exact mul_nonneg (by exact_mod_cast L_nonneg u a b n (by omega))
    (rising_nonneg (by linarith) n)

end Abdesselam
