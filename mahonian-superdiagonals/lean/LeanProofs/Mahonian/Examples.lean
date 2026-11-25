import LeanProofs.Mahonian.Truncation

/-!
# Tests: `P_1` and `P_2` against the printed polynomials

The note (and CFS) print `P_1 = -1 + 2x` and `P_2 = -1 + 4x - 4x^2 + x^3 + x^4`. Here they are
derived from the definition of `P` using the small values `f_0 = 1`, `f_1 = -1`, `A(-1,0) = A(-2,0)
= 1`, `A(-1,1) = -2` and `c_0 = 1` for `i = 2` (Lemma 2, `c_sub_two`).
-/

set_option linter.style.longLine false

namespace Mahonian

lemma f_zero : f 0 = 1 := by simp [f, E]

lemma f_one : f 1 = -1 := by simp [f, E, PowerSeries.coeff_X]

lemma Aneg_zero (r : ℕ) : Aneg r 0 = 1 := by
  simp only [Aneg, PowerSeries.coeff_zero_eq_constantCoeff_apply, map_mul, map_pow, map_sub, map_one, PowerSeries.constantCoeff_X,
    sub_zero, one_pow, mul_one]
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, F, PowerSeries.coeff_mk, f_zero]

lemma Aneg_one_one : Aneg 1 1 = -2 := by
  rw [Aneg, pow_one, mul_sub, mul_one, map_sub, PowerSeries.coeff_succ_mul_X, F, PowerSeries.coeff_mk,
    PowerSeries.coeff_mk, f_zero, f_one]
  norm_num

open Polynomial in
/-- `P_1 = -1 + 2x`. -/
theorem P_one : P 1 = -1 + 2 * X := by
  simp only [P, Nat.sub_self, Finset.range_zero, Finset.sum_empty, Finset.Icc_self, Finset.sum_singleton,
    Finset.range_one, pow_zero, pow_one, Aneg_zero, f_zero, map_one, add_zero]
  ring

open Polynomial in
/-- `P_2 = -1 + 4x - 4x^2 + x^3 + x^4`. -/
theorem P_two : P 2 = -1 + 4 * X - 4 * X ^ 2 + X ^ 3 + X ^ 4 := by
  have hc : c 2 0 = 1 := c_sub_two le_rfl
  have hI : Finset.Icc 1 2 = {1, 2} := by decide
  simp only [P, hI, Finset.sum_insert (by decide : (1 : ℕ) ∉ ({2} : Finset ℕ)), Finset.sum_singleton,
    Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, hc, f_zero, f_one]
  norm_num [Aneg_zero, Aneg_one_one]
  ring

end Mahonian
