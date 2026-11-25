import LeanProofs.Mahonian.Defs

/-!
# Lemma 4 of the note: the columns `∑_n A(n,t) x^n`

The paper expands `∑_n x^n φ(q)^n = (1-q)/(1-x-q)` in `q`: the coefficient of `q^u` is `1/(1-x)` for
`u = 0` and `x (1-x)^{-u-1}` for `u ≥ 1`. We prove the same column identities `colGeom` without
two-variable series, by the recurrence `φ^{n+1} (1-q) = φ^n`, then multiply by `F` and take the
coefficient of `q^t`.
-/

set_option linter.style.longLine false

open PowerSeries

namespace Mahonian

noncomputable section

/-- The column `∑_n ([q^u] φ(q)^n) x^n`. -/
def colGeom (u : ℕ) : PowerSeries ℤ := mk fun n => coeff u (geom ^ n)

lemma colGeom_zero : colGeom 0 = geom := by
  ext n
  simp [colGeom, coeff_zero_eq_constantCoeff_apply, map_pow, geom]

/-- `(1 - x) · col_{u+1} = col_u - [u = 0]`, from `φ^{n+1} (1-q) = φ^n`. -/
lemma colGeom_succ (u : ℕ) :
    (1 - X) * colGeom (u + 1) = colGeom u - C (coeff u (1 : PowerSeries ℤ)) := by
  ext n
  cases n with
  | zero =>
    simp [colGeom, sub_mul, coeff_one, coeff_zero_eq_constantCoeff_apply]
  | succ n =>
    have key : geom ^ (n + 1) * (1 - X) = geom ^ n := by
      rw [pow_succ, mul_assoc, geom_mul_one_sub, mul_one]
    have hk := congrArg (coeff (u + 1)) key
    rw [mul_sub, mul_one, map_sub, coeff_succ_mul_X] at hk
    rw [sub_mul, one_mul, map_sub, map_sub, X_mul, coeff_succ_mul_X, coeff_C]
    simp only [colGeom, coeff_mk, Nat.add_one_ne_zero, ite_false, sub_zero]
    linarith

/-- The column identity for `u ≥ 1`: `(1-x)^{u+1} col_u = x`, i.e. `col_u = x (1-x)^{-u-1}`. -/
lemma colGeom_pos (u : ℕ) : (1 - X) ^ (u + 2) * colGeom (u + 1) = X := by
  induction u with
  | zero =>
    rw [pow_two, mul_assoc, colGeom_succ, colGeom_zero, coeff_one, ite_eq_left rfl, map_one, mul_sub,
      one_sub_mul_geom, mul_one]; ring
  | succ u ih =>
    rw [show (1 - X : PowerSeries ℤ) ^ (u + 1 + 2) = (1 - X) ^ (u + 2) * (1 - X) by ring, mul_assoc,
      colGeom_succ, coeff_one, ite_eq_right (by omega), map_zero, sub_zero, ih]

/-- The column of `A`, expanded in Euler's coefficients. -/
lemma colA_expand (t : ℕ) :
    (mk fun n => A n t) = ∑ p ∈ Finset.HasAntidiagonal.antidiagonal t, C (f p.1) * colGeom p.2 := by
  ext n
  rw [coeff_mk, A, coeff_mul, map_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [coeff_C_mul, colGeom, coeff_mk, F, coeff_mk]

/-- **Lemma 4.** `(1-x)^{t+1} ∑_n A(n,t) x^n = f_t (1-x)^t + ∑_{s=0}^{t-1} f_s x (1-x)^s`, i.e.
`∑_n A(n,t) x^n = f_t/(1-x) + ∑_{s<t} f_s x/(1-x)^{t-s+1}`. -/
theorem lemma4 (t : ℕ) :
    (1 - X) ^ (t + 1) * (mk fun n => A n t)
      = C (f t) * (1 - X) ^ t + ∑ s ∈ Finset.range t, C (f s) * X * (1 - X) ^ s := by
  rw [colA_expand, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_range_succ, mul_add,
    Finset.mul_sum, add_comm]
  congr 1
  · rw [Nat.sub_self, colGeom_zero, pow_succ]
    linear_combination (C (f t) * (1 - X) ^ t) * one_sub_mul_geom
  · refine Finset.sum_congr rfl fun s hs => ?_
    obtain ⟨u, hu⟩ : ∃ u, t - s = u + 1 := ⟨t - s - 1, by simp at hs; omega⟩
    have ht : t + 1 = s + (u + 2) := by simp at hs; omega
    rw [hu, ht, pow_add]
    linear_combination (C (f s) * (1 - X) ^ s) * colGeom_pos u

end

end Mahonian
