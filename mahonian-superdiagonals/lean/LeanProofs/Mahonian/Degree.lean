import LeanProofs.Mahonian.Truncation

/-!
# Theorem 1 of the note: degree and leading coefficient of `P_i`

The note's degree argument. For `i ≥ 2` the term `(1-x)^i c_{i-2} x^{2i-2}` has degree `3i-2` and
leading coefficient `(-1)^i c_{i-2} = (-1)^i` (Lemma 2, `c_sub_two`). Every other term of `P_i` has
degree at most `3i-3`: the terms `c_n x^{n+i} (1-x)^i` with `n ≤ i-3` (degree `≤ 3i-3`), the terms
`A(-r,i-r) x^{i-r} (1-x)^i` (degree `≤ 2i-1`) and the last double sum (degree `≤ 2i-1`); and
`2i-1 ≤ 3i-3` for `i ≥ 2`.
-/

set_option linter.style.longLine false

open Polynomial

namespace Mahonian

noncomputable section

lemma natDegree_term_le {z : ℤ} {a b d : ℕ} (h : a + b ≤ d) :
    (C z * X ^ a * (1 - X) ^ b : ℤ[X]).natDegree ≤ d := by
  have h1 : (1 - X : ℤ[X]).natDegree ≤ 1 := by
    refine (natDegree_sub_le _ _).trans ?_; simp
  have h2 := natDegree_pow_le_of_le b h1
  refine (natDegree_mul_le).trans ?_
  have := natDegree_C_mul_X_pow_le z a
  omega

/-- The leading part `(1-x)^i x^{2i-2}` of `P_i`. -/
lemma lead_part (a b : ℕ) :
    ((1 - X : ℤ[X]) ^ a * X ^ b).natDegree = a + b ∧ ((1 - X : ℤ[X]) ^ a * X ^ b).leadingCoeff = (-1) ^ a := by
  have hm : ((X - C 1 : ℤ[X]) ^ a * X ^ b).Monic := ((monic_X_sub_C 1).pow a).mul (monic_X_pow b)
  have hd : ((X - C 1 : ℤ[X]) ^ a * X ^ b).natDegree = a + b := by
    rw [((monic_X_sub_C 1).pow a).natDegree_mul (monic_X_pow b), (monic_X_sub_C 1).natDegree_pow,
      natDegree_X_sub_C, natDegree_X_pow, mul_one]
  have he : (1 - X : ℤ[X]) ^ a * X ^ b = C ((-1) ^ a) * ((X - C 1) ^ a * X ^ b) := by
    rw [map_pow, map_neg, map_one, ← mul_assoc, ← mul_pow, neg_one_mul, neg_sub]
  rw [he]
  refine ⟨?_, ?_⟩
  · rw [natDegree_C_mul (pow_ne_zero _ (by norm_num)), hd]
  · rw [leadingCoeff_C_mul_of_isUnit (isUnit_one.neg.pow a), hm.leadingCoeff, mul_one]

/-- `P_{k+2}` split into its leading part and a remainder of degree `≤ 3k+3`. -/
lemma P_split (k : ℕ) :
    P (k + 2) = (1 - X) ^ (k + 2) * X ^ (2 * k + 2)
      + (∑ n ∈ Finset.range k, C (c (k + 2) n) * X ^ (n + (k + 2)) * (1 - X) ^ (k + 2)
        - ∑ r ∈ Finset.Icc 1 (k + 2), C (Aneg r (k + 2 - r)) * X ^ (k + 2 - r) * (1 - X) ^ (k + 2)
        + ∑ t ∈ Finset.range (k + 2), (C (f t) * X ^ (k + 2) * (1 - X) ^ (k + 2 - 1)
          + ∑ s ∈ Finset.range t, C (f s) * X ^ (k + 2 + 1) * (1 - X) ^ (k + 2 - t + s - 1))) := by
  have hc : c (k + 2) k = 1 := by simpa using c_sub_two (i := k + 2) (by omega)
  have e1 : (1 - X : ℤ[X]) ^ (k + 2) * ∑ n ∈ Finset.range k, C (c (k + 2) n) * X ^ (n + (k + 2))
      = ∑ n ∈ Finset.range k, C (c (k + 2) n) * X ^ (n + (k + 2)) * (1 - X) ^ (k + 2) := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring
  have e2 : (1 - X : ℤ[X]) ^ (k + 2) * ∑ r ∈ Finset.Icc 1 (k + 2), C (Aneg r (k + 2 - r)) * X ^ (k + 2 - r)
      = ∑ r ∈ Finset.Icc 1 (k + 2), C (Aneg r (k + 2 - r)) * X ^ (k + 2 - r) * (1 - X) ^ (k + 2) := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring
  have e3 : (X : ℤ[X]) ^ (k + 2) * ∑ t ∈ Finset.range (k + 2), (C (f t) * (1 - X) ^ (k + 2 - 1)
        + ∑ s ∈ Finset.range t, C (f s) * X * (1 - X) ^ (k + 2 - t + s - 1))
      = ∑ t ∈ Finset.range (k + 2), (C (f t) * X ^ (k + 2) * (1 - X) ^ (k + 2 - 1)
          + ∑ s ∈ Finset.range t, C (f s) * X ^ (k + 2 + 1) * (1 - X) ^ (k + 2 - t + s - 1)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [mul_add, Finset.mul_sum]
    exact congrArg₂ (· + ·) (by ring) (Finset.sum_congr rfl fun _ _ => by ring)
  have e0 : ∑ n ∈ Finset.range (k + 2 - 1), C (c (k + 2) n) * (X : ℤ[X]) ^ (n + (k + 2))
      = ∑ n ∈ Finset.range k, C (c (k + 2) n) * X ^ (n + (k + 2)) + X ^ (2 * k + 2) := by
    rw [show k + 2 - 1 = k + 1 by omega, Finset.sum_range_succ (fun n => C (c (k + 2) n) * (X : ℤ[X]) ^ (n + (k + 2))) k,
      hc, map_one, one_mul, show k + (k + 2) = 2 * k + 2 by omega]
  unfold P
  rw [e0]
  linear_combination e1 - e2 + e3

lemma rest_natDegree_le (k : ℕ) :
    (∑ n ∈ Finset.range k, C (c (k + 2) n) * X ^ (n + (k + 2)) * (1 - X) ^ (k + 2)
        - ∑ r ∈ Finset.Icc 1 (k + 2), C (Aneg r (k + 2 - r)) * X ^ (k + 2 - r) * (1 - X) ^ (k + 2)
        + ∑ t ∈ Finset.range (k + 2), (C (f t) * X ^ (k + 2) * (1 - X) ^ (k + 2 - 1)
          + ∑ s ∈ Finset.range t, C (f s) * X ^ (k + 2 + 1) * (1 - X) ^ (k + 2 - t + s - 1)) : ℤ[X]).natDegree
      ≤ 3 * k + 3 := by
  refine natDegree_add_le_of_degree_le ((natDegree_sub_le_of_le ?_ ?_).trans (max_self _).le) ?_
  · exact natDegree_sum_le_of_forall_le _ _ fun n hn => natDegree_term_le (by simp at hn; omega)
  · exact natDegree_sum_le_of_forall_le _ _ fun r hr => natDegree_term_le (by simp at hr; omega)
  · refine natDegree_sum_le_of_forall_le _ _ fun t ht => natDegree_add_le_of_degree_le
      (natDegree_term_le (by omega)) (natDegree_sum_le_of_forall_le _ _ fun s hs => natDegree_term_le ?_)
    simp at ht hs; omega

/-- **Theorem 1, degree.** For `i ≥ 2`, `P_i` has degree exactly `3i-2`. -/
theorem natDegree_P {i : ℕ} (hi : 2 ≤ i) : (P i).natDegree = 3 * i - 2 := by
  obtain ⟨k, rfl⟩ : ∃ k, i = k + 2 := ⟨i - 2, by omega⟩
  rw [P_split, natDegree_add_eq_left_of_natDegree_lt, (lead_part _ _).1]
  · omega
  · rw [(lead_part _ _).1]; have := rest_natDegree_le k; omega

/-- **Theorem 1, leading coefficient.** For `i ≥ 2`, the leading coefficient of `P_i` is `(-1)^i`. -/
theorem leadingCoeff_P {i : ℕ} (hi : 2 ≤ i) : (P i).leadingCoeff = (-1) ^ i := by
  obtain ⟨k, rfl⟩ : ∃ k, i = k + 2 := ⟨i - 2, by omega⟩
  rw [P_split, leadingCoeff_add_of_degree_lt', (lead_part _ _).2]
  apply degree_lt_degree
  rw [(lead_part _ _).1]; have := rest_natDegree_le k; omega

end

end Mahonian
