import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.Tactic

/-!
# MO 467261 (Ait-Haddou): definitions and algebraic identities

Throughout `N = n - 1` (so `n = N + 1 ≥ 1`) and `y = x - 1`.
`P N y ℓ` is the polynomial in the index `t`
  `P_ℓ(t) = ∑_{k ≤ ℓ} C(N+ℓ, ℓ-k) y^k · t(t+1)⋯(t+k-1)/k!`,
which equals `h_ℓ(1^{[n-t]}, x^{[t]})` at `t = 0, …, n`.
-/

open Polynomial Finset

namespace Haddou

/-- Normalised rising factorial `t(t+1)⋯(t+k-1)/k!`. -/
noncomputable def b (k : ℕ) : ℝ[X] := C ((k.factorial : ℝ)⁻¹) * ascPochhammer ℝ k

/-- Coefficient `C(N+ℓ, ℓ-k) y^k` for `k ≤ ℓ`, zero beyond. -/
noncomputable def a (N : ℕ) (y : ℝ) (ℓ k : ℕ) : ℝ :=
  if k ≤ ℓ then ((N + ℓ).choose (ℓ - k) : ℝ) * y ^ k else 0

/-- The polynomial `P_ℓ(t)`. -/
noncomputable def P (N : ℕ) (y : ℝ) (ℓ : ℕ) : ℝ[X] := ∑ k ∈ range (ℓ + 1), C (a N y ℓ k) * b k

lemma a_of_lt {N : ℕ} {y : ℝ} {ℓ k : ℕ} (h : ℓ < k) : a N y ℓ k = 0 := by
  simp [a, Nat.not_le.mpr h]

lemma P_eq_sum (N : ℕ) (y : ℝ) {ℓ M : ℕ} (hM : ℓ + 1 ≤ M) :
    P N y ℓ = ∑ k ∈ range M, C (a N y ℓ k) * b k := by
  unfold P
  rw [← Finset.sum_range_add_sum_Ico _ hM]
  have : ∑ k ∈ Ico (ℓ + 1) M, C (a N y ℓ k) * b k = 0 :=
    Finset.sum_eq_zero fun k hk => by
      rw [a_of_lt (by simp at hk; omega), C_0, zero_mul]
  rw [this, add_zero]

/-- `X · b_k = (k+1) b_{k+1} - k b_k`. -/
lemma X_mul_b (k : ℕ) : X * b k = C ((k : ℝ) + 1) * b (k + 1) - C (k : ℝ) * b k := by
  unfold b
  rw [ascPochhammer_succ_right, Nat.factorial_succ]
  have hk : ((k.factorial : ℝ)) ≠ 0 := by positivity
  have hk1 : ((k : ℝ) + 1) ≠ 0 := by positivity
  have hnat : ((k : ℝ[X])) = C (k : ℝ) := by simp
  rw [hnat]
  push_cast
  have : C ((k : ℝ) + 1) * C (((k : ℝ) + 1) * (k.factorial : ℝ))⁻¹ = C ((k.factorial : ℝ)⁻¹) := by
    rw [← C_mul]; congr 1; field_simp
  calc X * (C ((k.factorial : ℝ))⁻¹ * ascPochhammer ℝ k)
      = C ((k : ℝ) + 1) * C (((k : ℝ) + 1) * (k.factorial : ℝ))⁻¹ * (ascPochhammer ℝ k * (X + C (k:ℝ)))
          - C (k : ℝ) * (C ((k.factorial : ℝ))⁻¹ * ascPochhammer ℝ k) := by rw [this]; ring
    _ = _ := by ring


/-- Pascal-type relations used in the recurrence, cast to `ℝ`. -/
lemma choose_rels (S j : ℕ) :
    ((S + 1 : ℕ) : ℝ) * (S.choose j) = ((S + 1).choose (j + 1)) * ((j : ℝ) + 1) ∧
    ((S + 2 : ℕ) : ℝ) * ((S + 1).choose (j + 1)) = ((S + 2).choose (j + 2)) * ((j : ℝ) + 2) ∧
    (((S + 1).choose (j + 2) : ℕ) : ℝ) * ((j : ℝ) + 2) =
      ((S + 1).choose (j + 1)) * (((S + 1 - (j + 1) : ℕ)) : ℝ) := by
  refine ⟨?_, ?_, ?_⟩
  · have := Nat.add_one_mul_choose_eq S j
    exact_mod_cast this
  · have := Nat.add_one_mul_choose_eq (S + 1) (j + 1)
    exact_mod_cast this
  · have := Nat.choose_succ_right_eq (S + 1) (j + 1)
    exact_mod_cast this

/-- Coefficientwise form of the three-term recurrence. -/
lemma coef_rec (N : ℕ) (y : ℝ) (ℓ k : ℕ) :
    ((ℓ : ℝ) + 2) * a N y (ℓ + 2) k =
      ((2 + y) * ((ℓ : ℝ) + 1) + N + 1) * a N y (ℓ + 1) k
        + y * ((k : ℝ) * a N y (ℓ + 1) (k - 1) - (k : ℝ) * a N y (ℓ + 1) k)
        - (1 + y) * ((N : ℝ) + ℓ + 1) * a N y ℓ k := by
  rcases Nat.lt_or_ge (ℓ + 2) k with h | h
  · rw [a_of_lt h, a_of_lt (by omega), a_of_lt (by omega), a_of_lt (by omega)]; ring
  rcases Nat.lt_or_ge ℓ k with h' | h'
  · -- k = ℓ + 1 or k = ℓ + 2
    rw [a_of_lt h']
    rcases (show k = ℓ + 1 ∨ k = ℓ + 2 by omega) with rfl | rfl
    · simp only [a, le_refl, ite_true, show ℓ + 1 ≤ ℓ + 2 by omega, show ℓ + 1 - 1 ≤ ℓ + 1 by omega,
        show ℓ + 2 - (ℓ + 1) = 1 by omega, Nat.sub_self, show ℓ + 1 - (ℓ + 1 - 1) = 1 by omega,
        Nat.choose_one_right, Nat.choose_zero_right]
      rw [show ℓ + 1 - 1 = ℓ by omega]
      push_cast; ring
    · simp only [a, le_refl, ite_true, show ¬ (ℓ + 2 ≤ ℓ + 1) by omega, ite_false,
        Nat.sub_self, show ℓ + 2 - 1 = ℓ + 1 by omega,
        Nat.choose_zero_right]
      push_cast; ring
  obtain ⟨j, rfl⟩ : ∃ j, ℓ = k + j := ⟨ℓ - k, by omega⟩
  obtain ⟨R1, R2, R3⟩ := choose_rels (N + k + j) j
  have hS : N + k + j + 1 - (j + 1) = N + k := by omega
  rw [hS] at R3
  have e1 : N + (k + j + 2) = N + k + j + 2 := by ring
  have e2 : N + (k + j + 1) = N + k + j + 1 := by ring
  have e3 : N + (k + j) = N + k + j := by ring
  have hA2 : a N y (k + j + 2) k = ((N + k + j + 2).choose (j + 2) : ℝ) * y ^ k := by
    simp only [a, show k ≤ k + j + 2 by omega, ite_true, show k + j + 2 - k = j + 2 by omega, e1]
  have hA1 : a N y (k + j + 1) k = ((N + k + j + 1).choose (j + 1) : ℝ) * y ^ k := by
    simp only [a, show k ≤ k + j + 1 by omega, ite_true, show k + j + 1 - k = j + 1 by omega, e2]
  have hA0 : a N y (k + j) k = ((N + k + j).choose j : ℝ) * y ^ k := by
    simp only [a, show k ≤ k + j by omega, ite_true, show k + j - k = j by omega, e3]
  have hAm : y * ((k : ℝ) * a N y (k + j + 1) (k - 1)) =
      (k : ℝ) * ((N + k + j + 1).choose (j + 2) : ℝ) * y ^ k := by
    rcases k with _ | k
    · simp
    · rw [show k + 1 - 1 = k by omega]
      simp only [a, show k ≤ k + 1 + j + 1 by omega, ite_true,
        show k + 1 + j + 1 - k = j + 2 by omega, show N + (k + 1 + j + 1) = N + (k + 1) + j + 1 by ring]
      push_cast; ring
  rw [hA2, hA1, hA0, mul_sub y, hAm]
  have hj1 : ((j : ℝ) + 1) ≠ 0 := by positivity
  have hj2 : ((j : ℝ) + 2) ≠ 0 := by positivity
  have hS1 : (((N + k + j + 1 : ℕ)) : ℝ) ≠ 0 := by positivity
  have hc : ((N + k + j).choose j : ℝ) = ((N + k + j + 1).choose (j + 1) : ℝ) * ((j : ℝ) + 1) /
      (((N + k + j + 1 : ℕ)) : ℝ) := by
    rw [eq_div_iff hS1, ← R1]; ring
  have hv : ((N + k + j + 2).choose (j + 2) : ℝ) =
      (((N + k + j + 2 : ℕ)) : ℝ) * ((N + k + j + 1).choose (j + 1) : ℝ) / ((j : ℝ) + 2) := by
    rw [eq_div_iff hj2, R2]
  have hw : ((N + k + j + 1).choose (j + 2) : ℝ) =
      ((N + k + j + 1).choose (j + 1) : ℝ) * (((N + k : ℕ)) : ℝ) / ((j : ℝ) + 2) := by
    rw [eq_div_iff hj2, R3]
  rw [hc, hv, hw]
  push_cast at hS1 ⊢
  field_simp
  ring

lemma shift_sum (N : ℕ) (y : ℝ) (ℓ : ℕ) :
    ∑ k ∈ range (ℓ + 3), C (a N y (ℓ + 1) k) * (C ((k : ℝ) + 1) * b (k + 1)) =
      ∑ k ∈ range (ℓ + 3), C ((k : ℝ) * a N y (ℓ + 1) (k - 1)) * b k := by
  have h1 := Finset.sum_range_succ' (fun k => C ((k : ℝ) * a N y (ℓ + 1) (k - 1)) * b k) (ℓ + 3)
  have h2 := Finset.sum_range_succ (fun k => C ((k : ℝ) * a N y (ℓ + 1) (k - 1)) * b k) (ℓ + 3)
  have hM : a N y (ℓ + 1) (ℓ + 3 - 1) = 0 := a_of_lt (by omega)
  simp only [hM, mul_zero, C_0, zero_mul, add_zero, Nat.cast_zero, zero_mul] at h1 h2
  rw [← h2, h1]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one, C_mul]
  ring

/-- The three-term recurrence in `ℓ` (coefficient of `t` is `y/(ℓ+2)·(ℓ+2)`). -/
theorem P_rec (N : ℕ) (y : ℝ) (ℓ : ℕ) :
    C ((ℓ : ℝ) + 2) * P N y (ℓ + 2) =
      (C ((2 + y) * ((ℓ : ℝ) + 1) + N + 1) + C y * X) * P N y (ℓ + 1)
        - C ((1 + y) * ((N : ℝ) + ℓ + 1)) * P N y ℓ := by
  rw [P_eq_sum N y (M := ℓ + 3) (by omega), P_eq_sum N y (M := ℓ + 3) (by omega),
    P_eq_sum N y (M := ℓ + 3) (by omega)]
  have hX : X * ∑ k ∈ range (ℓ + 3), C (a N y (ℓ + 1) k) * b k =
      ∑ k ∈ range (ℓ + 3), C ((k : ℝ) * a N y (ℓ + 1) (k - 1)) * b k
        - ∑ k ∈ range (ℓ + 3), C ((k : ℝ) * a N y (ℓ + 1) k) * b k := by
    rw [← shift_sum, mul_sum, ← sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [show X * (C (a N y (ℓ + 1) k) * b k) = C (a N y (ℓ + 1) k) * (X * b k) by ring, X_mul_b]
    simp only [C_mul]; ring
  rw [add_mul, mul_assoc, hX, mul_sum, mul_sum, mul_sum, mul_sub, mul_sum, mul_sum,
    ← sum_sub_distrib, ← sum_add_distrib, ← sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← mul_assoc, ← C_mul, coef_rec]
  simp only [C_add, C_sub, C_mul]
  ring

lemma P_zero (N : ℕ) (y : ℝ) : P N y 0 = 1 := by
  simp [P, a, b, ascPochhammer_zero]

lemma P_one (N : ℕ) (y : ℝ) : P N y 1 = C ((N : ℝ) + 1) + C y * X := by
  simp [P, a, b, Finset.sum_range_succ, ascPochhammer_zero, ascPochhammer_one]

lemma b_eval_nonneg (k : ℕ) {t : ℝ} (ht : 0 ≤ t) : 0 ≤ (b k).eval t := by
  unfold b
  rw [eval_mul, eval_C]
  rcases ht.lt_or_eq with ht | rfl
  · exact mul_nonneg (by positivity) (ascPochhammer_pos k t ht).le
  · rw [ascPochhammer_eval_zero]; split_ifs <;> positivity

lemma P_eval_pos (N : ℕ) {y : ℝ} (hy : 0 ≤ y) (ℓ : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    0 < (P N y ℓ).eval t := by
  unfold P
  rw [eval_finsetSum, Finset.sum_range_succ']
  have h0 : 0 < (C (a N y ℓ 0) * b 0).eval t := by
    simp only [a, b, Nat.zero_le, ite_true, Nat.sub_zero, pow_zero, mul_one, Nat.factorial_zero,
      Nat.cast_one, inv_one, C_1, ascPochhammer_zero, eval_C]
    exact_mod_cast Nat.choose_pos (by omega)
  refine add_pos_of_nonneg_of_pos (Finset.sum_nonneg fun k _ => ?_) h0
  rw [eval_mul, eval_C]
  refine mul_nonneg ?_ (b_eval_nonneg _ ht)
  unfold a; split_ifs <;> positivity

lemma natDegree_b (k : ℕ) : (b k).natDegree = k := by
  unfold b
  rw [natDegree_C_mul (by positivity), ascPochhammer_natDegree]

lemma leadingCoeff_b (k : ℕ) : (b k).leadingCoeff = ((k.factorial : ℝ))⁻¹ := by
  unfold b
  rw [leadingCoeff_C_mul_of_isUnit (by simp; positivity), (monic_ascPochhammer ℝ k).leadingCoeff, mul_one]

lemma b_ne_zero (k : ℕ) : b k ≠ 0 := by
  intro h; have := leadingCoeff_b k; rw [h, leadingCoeff_zero] at this
  exact (by positivity : (0:ℝ) < ((k.factorial : ℝ))⁻¹).ne this

lemma degree_b (k : ℕ) : (b k).degree = k := by
  rw [degree_eq_natDegree (b_ne_zero k), natDegree_b]

lemma P_split (N : ℕ) (y : ℝ) (ℓ : ℕ) :
    P N y ℓ = ∑ k ∈ range ℓ, C (a N y ℓ k) * b k + C (y ^ ℓ) * b ℓ := by
  rw [P, Finset.sum_range_succ]
  congr 2
  simp [a]

lemma degree_low_lt (N : ℕ) (y : ℝ) (ℓ : ℕ) :
    (∑ k ∈ range ℓ, C (a N y ℓ k) * b k).degree < ℓ := by
  refine lt_of_le_of_lt (degree_sum_le _ _) ?_
  refine (Finset.sup_lt_iff (WithBot.bot_lt_coe ℓ)).2 fun k hk => ?_
  refine lt_of_le_of_lt degree_le_natDegree ?_
  refine WithBot.coe_lt_coe.2 (lt_of_le_of_lt (natDegree_C_mul_le _ _) ?_)
  rw [natDegree_b]; exact Finset.mem_range.1 hk

lemma natDegree_P (N : ℕ) {y : ℝ} (hy : y ≠ 0) (ℓ : ℕ) : (P N y ℓ).natDegree = ℓ := by
  rw [P_split]
  have hdeg : (C (y ^ ℓ) * b ℓ).degree = ℓ := by
    rw [degree_C_mul (pow_ne_zero _ hy), degree_b]
  rw [natDegree_add_eq_right_of_degree_lt (by rw [hdeg]; exact degree_low_lt N y ℓ)]
  exact natDegree_eq_of_degree_eq_some hdeg

lemma leadingCoeff_P (N : ℕ) {y : ℝ} (hy : y ≠ 0) (ℓ : ℕ) :
    (P N y ℓ).leadingCoeff = y ^ ℓ * ((ℓ.factorial : ℝ))⁻¹ := by
  rw [P_split]
  have hdeg : (C (y ^ ℓ) * b ℓ).degree = ℓ := by
    rw [degree_C_mul (pow_ne_zero _ hy), degree_b]
  rw [leadingCoeff_add_of_degree_lt (by rw [hdeg]; exact degree_low_lt N y ℓ),
    leadingCoeff_C_mul_of_isUnit (by simp [hy]), leadingCoeff_b]

/-- Wronskian of consecutive members: `W_ℓ = P_{ℓ+1}' P_ℓ - P_{ℓ+1} P_ℓ'`. -/
noncomputable def W (N : ℕ) (y : ℝ) (ℓ : ℕ) : ℝ[X] :=
  derivative (P N y (ℓ + 1)) * P N y ℓ - P N y (ℓ + 1) * derivative (P N y ℓ)

lemma W_zero (N : ℕ) (y : ℝ) : W N y 0 = C y := by
  simp [W, P_zero, P_one]

/-- Christoffel–Darboux step: `(ℓ+2) W_{ℓ+1} = y P_{ℓ+1}^2 + (1+y)(N+ℓ+1) W_ℓ`. -/
lemma W_rec (N : ℕ) (y : ℝ) (ℓ : ℕ) :
    C ((ℓ : ℝ) + 2) * W N y (ℓ + 1) =
      C y * P N y (ℓ + 1) ^ 2 + C ((1 + y) * ((N : ℝ) + ℓ + 1)) * W N y ℓ := by
  have h := P_rec N y ℓ
  have hd := congrArg derivative h
  simp only [derivative_mul, derivative_C, zero_mul, zero_add, derivative_sub, derivative_add,
    derivative_X, mul_one] at hd
  unfold W
  linear_combination P N y (ℓ + 1) * hd - derivative (P N y (ℓ + 1)) * h

lemma W_pos (N : ℕ) {y : ℝ} (hy : 0 < y) (ℓ : ℕ) (t : ℝ) : 0 < (W N y ℓ).eval t := by
  induction ℓ with
  | zero => simpa [W_zero] using hy
  | succ ℓ ih =>
    have h := congrArg (eval t) (W_rec N y ℓ)
    simp only [eval_mul, eval_C, eval_add, eval_pow] at h
    have hl : (0 : ℝ) < (ℓ : ℝ) + 2 := by positivity
    have : 0 < ((ℓ : ℝ) + 2) * (W N y (ℓ + 1)).eval t := by
      rw [h]; positivity
    exact pos_of_mul_pos_right this hl.le

end Haddou
