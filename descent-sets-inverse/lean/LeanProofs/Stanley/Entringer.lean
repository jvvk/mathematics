import LeanProofs.Stanley.AltBasic
import Mathlib.RingTheory.Polynomial.Bernstein
import Mathlib.Data.List.GetD

namespace Stanley.Alt

open Finset Polynomial
open scoped Nat

theorem length_row (n : ℕ) : (row n).length = n + 1 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [row, ih]

def entry (n k : ℕ) : ℕ := (row n).getD k 0

theorem entry_succ_zero (n : ℕ) : entry (n + 1) 0 = 0 := by
  simp [entry, row, List.getD]

theorem entry_succ_succ {n k : ℕ} (hk : k ≤ n) :
    entry (n + 1) (k + 1) = entry (n + 1) k + entry n (n - k) := by
  have hl : k < (row n).reverse.length := by simp [length_row]; omega
  have hs : k + 1 < (List.scanl (· + ·) 0 (row n).reverse).length := by
    simpa only [List.length_scanl] using Nat.add_lt_add_right hl 1
  unfold entry
  rw [row]
  rw [List.getD_eq_getElem _ _ hs,
    List.getD_eq_getElem _ _ (Nat.lt_trans (Nat.lt_succ_self k) hs),
    List.getD_eq_getElem _ _ (by rw [length_row]; omega)]
  rw [List.getElem_succ_scanl hs, List.getElem_reverse]
  simp only [length_row, Nat.add_sub_cancel_right]

/-- The Entringer row in the Bernstein basis, without factorial normalization. -/
noncomputable def rowPoly (n : ℕ) : ℚ[X] :=
  ∑ k ∈ range (n + 1), C (entry n k : ℚ) * bernsteinPolynomial ℚ n k

theorem rowPoly_zero : rowPoly 0 = 1 := by
  simp [rowPoly, entry, row, bernsteinPolynomial]

theorem rowPoly_eval_zero (n : ℕ) : (rowPoly (n + 1)).eval 0 = 0 := by
  simp [rowPoly, Polynomial.eval_finsetSum, bernsteinPolynomial.eval_at_0, entry_succ_zero]

theorem rowPoly_eval_one (n : ℕ) : (rowPoly n).eval 1 = (E n : ℚ) := by
  simp [rowPoly, Polynomial.eval_finsetSum, bernsteinPolynomial.eval_at_1, entry, E]

theorem rowPoly_comp (n : ℕ) :
    (rowPoly n).comp (1 - X) =
      ∑ k ∈ range (n + 1), C (entry n (n - k) : ℚ) * bernsteinPolynomial ℚ n k := by
  simp only [rowPoly, Polynomial.sum_comp, Polynomial.mul_comp, Polynomial.C_comp]
  trans ∑ k ∈ range (n + 1), C (entry n k : ℚ) * bernsteinPolynomial ℚ n (n - k)
  · apply sum_congr rfl
    intro k hk
    rw [bernsteinPolynomial.flip _ _ _ (by simp only [mem_range] at hk; omega)]
  · rw [← Finset.sum_range_reflect]
    apply sum_congr rfl
    intro k hk
    simp only [mem_range] at hk
    congr 2; omega

theorem derivative_rowPoly (n : ℕ) :
    derivative (rowPoly (n + 1)) = C (n + 1 : ℚ) * (rowPoly n).comp (1 - X) := by
  rw [rowPoly, sum_range_succ']
  simp only [entry_succ_zero, Nat.cast_zero, C_0, zero_mul, add_zero,
    derivative_sum, derivative_C_mul, bernsteinPolynomial.derivative_succ_aux]
  have hshift : (∑ k ∈ range (n + 1), C (entry (n + 1) (k + 1) : ℚ) *
      bernsteinPolynomial ℚ n (k + 1)) =
      ∑ k ∈ range (n + 1), C (entry (n + 1) k : ℚ) * bernsteinPolynomial ℚ n k := by
    rw [sum_range_succ, bernsteinPolynomial.eq_zero_of_lt _ (by omega), mul_zero, add_zero]
    conv_rhs => rw [sum_range_succ']
    simp [entry_succ_zero]
  calc
    (∑ k ∈ range (n + 1), C (entry (n + 1) (k + 1) : ℚ) *
      ((n + 1) * (bernsteinPolynomial ℚ n k - bernsteinPolynomial ℚ n (k + 1)))) =
      C (n + 1 : ℚ) * (∑ k ∈ range (n + 1), C (entry (n + 1) (k + 1) : ℚ) *
        bernsteinPolynomial ℚ n k -
        ∑ k ∈ range (n + 1), C (entry (n + 1) (k + 1) : ℚ) *
          bernsteinPolynomial ℚ n (k + 1)) := by
        rw [mul_sub, mul_sum, mul_sum, ← sum_sub_distrib]
        apply sum_congr rfl
        intro k _
        simp only [C_add, C_eq_natCast, map_one]
        ring
    _ = C (n + 1 : ℚ) * (∑ k ∈ range (n + 1),
      C (entry n (n - k) : ℚ) * bernsteinPolynomial ℚ n k) := by
        rw [hshift, ← sum_sub_distrib]
        congr 1
        apply sum_congr rfl
        intro k hk
        rw [entry_succ_succ (by simp only [mem_range] at hk; omega)]
        push_cast
        simp only [C_add]
        ring
    _ = _ := by rw [rowPoly_comp]

/-! The continuous polynomial form of the Entringer triangle. -/

noncomputable def normalizedRow (n : ℕ) (x : ℝ) : ℝ :=
  aeval x (rowPoly n) / n !

theorem normalizedRow_zero (x : ℝ) : normalizedRow 0 x = 1 := by
  simp [normalizedRow, rowPoly_zero]

theorem normalizedRow_at_zero (n : ℕ) : normalizedRow (n + 1) 0 = 0 := by
  have h : aeval (0 : ℝ) (rowPoly (n + 1)) = 0 := by
    rw [← Polynomial.eval_map_algebraMap, Polynomial.eval_zero_map, rowPoly_eval_zero]
    simp
  simp [normalizedRow, h]

theorem normalizedRow_at_one (n : ℕ) : normalizedRow n 1 = (E n : ℝ) / n ! := by
  have h : aeval (1 : ℝ) (rowPoly n) = (E n : ℝ) := by
    rw [← Polynomial.eval_map_algebraMap, Polynomial.eval_one_map, rowPoly_eval_one]
    simp
  rw [normalizedRow, h]

theorem hasDerivAt_normalizedRow (n : ℕ) (x : ℝ) :
    HasDerivAt (normalizedRow (n + 1)) (normalizedRow n (1 - x)) x := by
  have h := (((rowPoly (n + 1)).map (algebraMap ℚ ℝ)).hasDerivAt x).div_const
    (((n + 1)! : ℕ) : ℝ)
  convert h using 1
  · ext y; simp [normalizedRow, Polynomial.eval_map_algebraMap]
  · simp only [Polynomial.derivative_map, derivative_rowPoly, Polynomial.map_mul,
      Polynomial.map_C, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.map_comp,
      Polynomial.eval_comp, Polynomial.map_sub, Polynomial.map_one, Polynomial.map_X,
      Polynomial.eval_sub, Polynomial.eval_one, Polynomial.eval_X,
      Polynomial.eval_map_algebraMap, normalizedRow]
    push_cast
    rw [Nat.factorial_succ]
    push_cast
    field_simp

end Stanley.Alt
