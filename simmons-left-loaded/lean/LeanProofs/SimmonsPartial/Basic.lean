import Mathlib

/-!
# Weights, the sequence `A` and its first differences

`X ~ Bin(n, m/n)` and `q = n - m`. Scaling by `n ^ n` makes every probability an integer:
`P(X = j) = w n m j / n ^ n` with `w n m j = C(n, j) m^j q^(n-j)`. The scaled Simmons gap is

  `A n m i = Σ_{j ≤ m - i} w j - Σ_{m + i ≤ j ≤ n} w j = n ^ n (P(X ≤ m - i) - P(X ≥ m + i))`,

with the first sum empty once `i > m`. This file proves the adjacent-mass identity
`(j + 1) q w (j + 1) = (n - j) m w j` (step (4) of the proof uses it), the difference
`A (i + 1) = A i + d i` with `d i = w (m + i) - w (m - i)` (step (1)), and the last value
`A q = - w n` when `q > m` (step (3)).
-/

namespace SimmonsPartial

open Finset

/-- `n ^ n P(X = j)` for `X ~ Bin(n, m/n)`. -/
def w (n m j : ℕ) : ℕ := n.choose j * m ^ j * (n - m) ^ (n - j)

/-- `n ^ n α_i = n ^ n (P(X ≤ m - i) - P(X ≥ m + i))`. -/
def A (n m i : ℕ) : ℤ :=
  (∑ j ∈ (range (n + 1)).filter (fun j => j + i ≤ m), (w n m j : ℤ)) -
    ∑ j ∈ (range (n + 1)).filter (fun j => m + i ≤ j), (w n m j : ℤ)

/-- The first difference `A (i + 1) - A i`; the lower mass `w (m - i)` is absent once `i > m`. -/
def d (n m i : ℕ) : ℤ := (w n m (m + i) : ℤ) - if i ≤ m then (w n m (m - i) : ℤ) else 0

lemma w_eq_zero {n m j : ℕ} (h : n < j) : w n m j = 0 := by
  simp [w, Nat.choose_eq_zero_of_lt h]

lemma w_pos {n m j : ℕ} (hm : 0 < m) (hmn : m < n) (hj : j ≤ n) : 0 < w n m j :=
  Nat.mul_pos (Nat.mul_pos (Nat.choose_pos hj) (pow_pos hm _)) (pow_pos (by omega) _)

/-- **Adjacent masses.** `(j + 1) q w (j + 1) = (n - j) m w j`, i.e.
`P(X = j + 1) / P(X = j) = (n - j) p / ((j + 1)(1 - p))`. -/
theorem adjacent (n m j : ℕ) :
    (j + 1) * (n - m) * w n m (j + 1) = (n - j) * m * w n m j := by
  rcases lt_or_ge j n with hj | hj
  · obtain ⟨k, hk⟩ : ∃ k, n - j = k + 1 := ⟨n - (j + 1), by omega⟩
    have hk' : n - (j + 1) = k := by omega
    have hc := Nat.choose_succ_right_eq n j
    rw [hk] at hc
    simp only [w, hk, hk']
    generalize n - m = q
    calc (j + 1) * q * (n.choose (j + 1) * m ^ (j + 1) * q ^ k)
        = (n.choose (j + 1) * (j + 1)) * m ^ j * m * q ^ k * q := by ring
      _ = (n.choose j * (k + 1)) * m ^ j * m * q ^ k * q := by rw [hc]
      _ = (k + 1) * m * (n.choose j * m ^ j * q ^ (k + 1)) := by ring
  · simp [w_eq_zero (show n < j + 1 by omega), Nat.sub_eq_zero_of_le hj]

/-- `A` as one sum over `0 ≤ j ≤ n`. -/
lemma A_eq (n m i : ℕ) : A n m i = ∑ j ∈ range (n + 1),
    ((if j + i ≤ m then (w n m j : ℤ) else 0) - if m + i ≤ j then (w n m j : ℤ) else 0) := by
  rw [A, sum_filter, sum_filter, ← sum_sub_distrib]

lemma sum_ite_eq_w (n m a : ℕ) :
    ∑ j ∈ range (n + 1), (if j = a then (w n m j : ℤ) else 0) = w n m a := by
  rw [sum_ite_eq']
  split_ifs with h
  · rfl
  · rw [w_eq_zero (by simp at h; omega)]; simp

/-- **Step (1).** `A (i + 1) = A i + w (m + i) - w (m - i)`, the second mass absent for `i > m`. -/
theorem A_succ (n m i : ℕ) : A n m (i + 1) = A n m i + d n m i := by
  have key : A n m (i + 1) - A n m i =
      ∑ j ∈ range (n + 1), (if j = m + i then (w n m j : ℤ) else 0) -
      ∑ j ∈ range (n + 1), (if j + i = m then (w n m j : ℤ) else 0) := by
    rw [A_eq, A_eq, ← sum_sub_distrib, ← sum_sub_distrib]
    refine sum_congr rfl fun j _ => ?_
    split_ifs <;> omega
  have h2 : ∑ j ∈ range (n + 1), (if j + i = m then (w n m j : ℤ) else 0) =
      if i ≤ m then (w n m (m - i) : ℤ) else 0 := by
    split_ifs with hi
    · rw [← sum_ite_eq_w n m (m - i)]
      refine sum_congr rfl fun j _ => ?_
      simp only [show j + i = m ↔ j = m - i by omega]
    · exact sum_eq_zero fun j _ => by rw [ite_eq_right (by omega)]
  rw [sum_ite_eq_w, h2] at key
  unfold d
  linarith

/-- **Step (3).** When `q > m`, `A q = - w n`: no `j ≤ m - q`, and only `j = n` has `j ≥ m + q`. -/
theorem A_last {n m : ℕ} (h : m < n - m) : A n m (n - m) = -(w n m n : ℤ) := by
  rw [A_eq, sum_range_succ, sum_eq_zero]
  · rw [ite_eq_right (by omega), ite_eq_left (by omega)]; ring
  · intro j hj
    simp only [mem_range] at hj
    rw [ite_eq_right (by omega), ite_eq_right (by omega)]; simp

/-- Beyond both ends, `A i = 0`. -/
lemma A_eq_zero {n m i : ℕ} (h1 : m < i) (h2 : n < m + i) : A n m i = 0 := by
  rw [A_eq]
  refine sum_eq_zero fun j hj => ?_
  simp only [mem_range] at hj
  rw [ite_eq_right (by omega), ite_eq_right (by omega)]; simp

end SimmonsPartial
