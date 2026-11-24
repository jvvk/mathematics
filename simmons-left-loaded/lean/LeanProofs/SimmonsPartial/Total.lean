import LeanProofs.SimmonsPartial.Basic

/-!
# Step (2): the gaps `A 1, ..., A q` sum to zero

`Σ_{i ≥ 1} P(X ≤ m - i) = E (m - X)^+` and `Σ_{i = 1}^{q} P(X ≥ m + i) = E (X - m)^+`, so the total is
`E (m - X) = 0`. In integers: swapping the double sum turns `Σ_{i=1}^{q} A i` into `Σ_j (m - j) w j`
(`j ≤ m - i` holds for exactly `m - j` values of `i` in `[1, q]` because `m ≤ q`, and `j ≥ m + i` for
exactly `j - m` values because `j ≤ n = m + q`). The mean identity `Σ_j j w j = m Σ_j w j` is
`E X = m`, obtained by summing the adjacent-mass identity over `j`.
-/

namespace SimmonsPartial

open Finset

lemma adjacent_int (n m j : ℕ) :
    ((j : ℤ) + 1) * ((n - m : ℕ) : ℤ) * w n m (j + 1) = ((n : ℤ) - j) * m * w n m j := by
  rcases le_or_gt j n with hj | hj
  · have h := adjacent n m j
    have h' : (((j + 1) * (n - m) * w n m (j + 1) : ℕ) : ℤ) = (((n - j) * m * w n m j : ℕ) : ℤ) := by
      rw [h]
    push_cast [Nat.cast_sub hj] at h'
    exact h'
  · rw [w_eq_zero hj, w_eq_zero (show n < j + 1 by omega)]; simp

lemma shift (n m : ℕ) : ∑ j ∈ range (n + 1), ((j : ℤ) + 1) * w n m (j + 1) =
    ∑ j ∈ range (n + 1), (j : ℤ) * w n m j := by
  have h1 : ∑ j ∈ range (n + 1 + 1), (j : ℤ) * w n m j = ∑ j ∈ range (n + 1), (j : ℤ) * w n m j := by
    rw [sum_range_succ, w_eq_zero (Nat.lt_succ_self n)]; simp
  have h2 : ∑ j ∈ range (n + 1 + 1), (j : ℤ) * w n m j =
      ∑ j ∈ range (n + 1), ((j : ℤ) + 1) * w n m (j + 1) := by
    rw [sum_range_succ']; push_cast; simp
  rw [← h2, h1]

/-- **The mean is `m`.** `Σ_j j w j = m Σ_j w j`, i.e. `E X = m`. -/
theorem mean {n m : ℕ} (hmn : m ≤ n) (hn : 0 < n) :
    ∑ j ∈ range (n + 1), (j : ℤ) * w n m j = m * ∑ j ∈ range (n + 1), (w n m j : ℤ) := by
  have hsum : ∑ j ∈ range (n + 1), ((j : ℤ) + 1) * ((n - m : ℕ) : ℤ) * w n m (j + 1) =
      ∑ j ∈ range (n + 1), ((n : ℤ) - j) * m * w n m j :=
    sum_congr rfl fun j _ => adjacent_int n m j
  have hL : ∑ j ∈ range (n + 1), ((j : ℤ) + 1) * ((n - m : ℕ) : ℤ) * w n m (j + 1) =
      ((n - m : ℕ) : ℤ) * ∑ j ∈ range (n + 1), (j : ℤ) * w n m j := by
    rw [← shift, mul_sum]; exact sum_congr rfl fun j _ => by ring
  have hR : ∑ j ∈ range (n + 1), ((n : ℤ) - j) * m * w n m j =
      m * (n * ∑ j ∈ range (n + 1), (w n m j : ℤ) - ∑ j ∈ range (n + 1), (j : ℤ) * w n m j) := by
    rw [mul_sum, ← sum_sub_distrib, mul_sum]; exact sum_congr rfl fun j _ => by ring
  rw [hL, hR] at hsum
  push_cast [hmn] at hsum
  have hn' : (n : ℤ) ≠ 0 := by exact_mod_cast hn.ne'
  apply mul_left_cancel₀ hn'
  linear_combination hsum

/-- For `j ≤ n` and `m ≤ q`, the column `j` of the double sum contributes `(m - j) w j`. -/
lemma column {n m j : ℕ} (hmq : m ≤ n - m) (hj : j ≤ n) :
    ∑ i ∈ Icc 1 (n - m), ((if j + i ≤ m then (w n m j : ℤ) else 0) - if m + i ≤ j then (w n m j : ℤ) else 0)
      = ((m : ℤ) - j) * w n m j := by
  rw [sum_sub_distrib, ← sum_filter, ← sum_filter, sum_const, sum_const, nsmul_eq_mul, nsmul_eq_mul]
  have e1 : (Icc 1 (n - m)).filter (fun i => j + i ≤ m) = Icc 1 (m - j) := by
    ext i; simp only [mem_filter, mem_Icc]; omega
  have e2 : (Icc 1 (n - m)).filter (fun i => m + i ≤ j) = Icc 1 (j - m) := by
    ext i; simp only [mem_filter, mem_Icc]; omega
  rw [e1, e2, Nat.card_Icc, Nat.card_Icc, ← sub_mul]
  congr 1
  omega

/-- **Step (2).** For `n ≥ 2m` (so `m ≤ q`), `Σ_{i=1}^{q} A i = 0`. -/
theorem total {n m : ℕ} (hn2 : 2 * m ≤ n) (hn : 0 < n) : ∑ i ∈ Icc 1 (n - m), A n m i = 0 := by
  simp only [A_eq]
  rw [sum_comm]
  rw [sum_congr rfl fun j hj => column (by omega) (by simp only [mem_range] at hj; omega)]
  simp only [sub_mul, sum_sub_distrib, ← mul_sum]
  rw [mean (by omega) hn]
  ring

end SimmonsPartial
