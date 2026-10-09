import Mathlib

/-!
# Representation functions of `ℕ ∖ E`: the coefficient bound (Proposition 1)

For `E ⊆ ℕ` let `D = ∑_{e ∈ E} Xᵉ`, `U = ∑ Xⁿ = 1/(1 - X)` and `G = U - D`, the membership series of
`A = ℕ ∖ E`. The ordered `h`-fold representation function is `R_{A,h}(N) = [X^N] G^h`
(Sándor–Yang, Section 1). With `m(N) = #(E ∩ [0, N])`:
* `key_identity`: `(1 - X) G³ = U² - 3 U D + 3 D² - (1 - X) D³`;
* `diff_ge`: `R_{A,3}(N) - R_{A,3}(N - 1) ≥ N + 1 - 3 m(N) - m(N)²` for `N ≥ 1`;
* `strictMono_of_three`: if `R_{A,3}` is strictly increasing from `0` and `0 ∈ A`, so is every
  `R_{A,h}`, `h ≥ 3`.
-/

open PowerSeries Finset

namespace SandorYang

variable (E : Set ℕ) [DecidablePred (· ∈ E)]

/-- Indicator of `E`. -/
def eps (n : ℕ) : ℤ := if n ∈ E then 1 else 0

/-- `D = ∑_{e ∈ E} Xᵉ`. -/
def D : ℤ⟦X⟧ := mk (eps E)

/-- `U = ∑ Xⁿ`. -/
def U : ℤ⟦X⟧ := mk 1

/-- The membership series of `A = ℕ ∖ E`. -/
def G : ℤ⟦X⟧ := U - D E

/-- `R_{A,h}(N)`, the number of ordered `h`-tuples from `A` with sum `N`. -/
noncomputable def R (h N : ℕ) : ℤ := coeff N (G E ^ h)

/-- `m(N) = #(E ∩ [0, N])`. -/
def m (N : ℕ) : ℕ := ((range (N + 1)).filter (· ∈ E)).card

lemma U_mul_one_sub : U * (1 - X : ℤ⟦X⟧) = 1 := mk_one_mul_one_sub_eq_one ℤ

theorem key_identity :
    (1 - X) * G E ^ 3 =
      U ^ 2 - 3 * U * D E + 3 * D E ^ 2 - (1 - X) * D E ^ 3 := by
  unfold G
  linear_combination (U ^ 2 - 3 * U * D E + 3 * D E ^ 2) * U_mul_one_sub

lemma coeff_one_sub_X_mul (F : ℤ⟦X⟧) (n : ℕ) :
    coeff (n + 1) ((1 - X) * F) = coeff (n + 1) F - coeff n F := by
  rw [sub_mul, one_mul, map_sub, coeff_succ_X_mul]

lemma coeff_zero_one_sub_X_mul (F : ℤ⟦X⟧) : coeff 0 ((1 - X) * F) = coeff 0 F := by
  rw [sub_mul, one_mul, map_sub, coeff_zero_X_mul, sub_zero]

lemma eps_nonneg (n : ℕ) : 0 ≤ eps E n := by unfold eps; split_ifs <;> norm_num

lemma eps_le_one (n : ℕ) : eps E n ≤ 1 := by unfold eps; split_ifs <;> norm_num

lemma coeff_D (n : ℕ) : coeff n (D E) = eps E n := coeff_mk _ _

lemma sum_eps (N : ℕ) : ∑ k ∈ range (N + 1), eps E k = (m E N : ℤ) := by
  simp only [eps, m]
  rw [Finset.sum_boole]

lemma m_mono {M N : ℕ} (h : M ≤ N) : m E M ≤ m E N :=
  Finset.card_le_card (Finset.filter_subset_filter _ (Finset.range_subset_range.2 (by omega)))

lemma coeff_U_sq (N : ℕ) : coeff N (U ^ 2 : ℤ⟦X⟧) = N + 1 := by
  rw [sq, coeff_mul]
  simp [U, Finset.Nat.card_antidiagonal]

lemma coeff_UD (N : ℕ) : coeff N (U * D E) = (m E N : ℤ) := by
  rw [mul_comm, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [coeff_D, U, coeff_mk, Pi.one_apply, mul_one]
  exact sum_eps E N

lemma coeff_D_sq_nonneg (N : ℕ) : 0 ≤ coeff N (D E ^ 2) := by
  rw [sq, coeff_mul]
  exact Finset.sum_nonneg fun p _ => by
    rw [coeff_D, coeff_D]; exact mul_nonneg (eps_nonneg E _) (eps_nonneg E _)

lemma coeff_D_sq_le (n : ℕ) : coeff n (D E ^ 2) ≤ (m E n : ℤ) := by
  rw [← sum_eps, sq, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  refine Finset.sum_le_sum fun k _ => ?_
  rw [coeff_D, coeff_D]
  calc eps E k * eps E (n - k) ≤ eps E k * 1 :=
        mul_le_mul_of_nonneg_left (eps_le_one E _) (eps_nonneg E _)
    _ = eps E k := mul_one _

lemma coeff_D_cube_nonneg (N : ℕ) : 0 ≤ coeff N (D E ^ 3) := by
  rw [pow_succ, coeff_mul]
  exact Finset.sum_nonneg fun p _ => by
    rw [coeff_D]; exact mul_nonneg (coeff_D_sq_nonneg E _) (eps_nonneg E _)

lemma coeff_D_cube_le (N : ℕ) : coeff N (D E ^ 3) ≤ (m E N : ℤ) ^ 2 := by
  rw [pow_succ, coeff_mul]
  calc ∑ p ∈ antidiagonal N, coeff p.1 (D E ^ 2) * coeff p.2 (D E)
      ≤ ∑ p ∈ antidiagonal N, (m E N : ℤ) * eps E p.2 := by
        refine Finset.sum_le_sum fun p hp => ?_
        rw [coeff_D]
        refine mul_le_mul_of_nonneg_right ((coeff_D_sq_le E _).trans ?_) (eps_nonneg E _)
        exact_mod_cast m_mono E (by have := (Finset.HasAntidiagonal.mem_antidiagonal).1 hp; omega)
    _ = (m E N : ℤ) * ∑ p ∈ antidiagonal N, eps E p.1 := by
        rw [← Finset.mul_sum, ← Finset.Nat.sum_antidiagonal_swap]; rfl
    _ = (m E N : ℤ) ^ 2 := by
        rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, sum_eps, sq]

lemma coeff_three_mul (F : ℤ⟦X⟧) (n : ℕ) : coeff n (3 * F) = 3 * coeff n F := by
  rw [show (3 : ℤ⟦X⟧) * F = F + F + F by ring, map_add, map_add]; ring

/-- Proposition 1, the bound: `R_{A,3}(N) - R_{A,3}(N - 1) ≥ N + 1 - 3 m(N) - m(N)²`. -/
theorem diff_ge (n : ℕ) :
    ((n + 1 : ℕ) : ℤ) + 1 - 3 * m E (n + 1) - (m E (n + 1) : ℤ) ^ 2 ≤ R E 3 (n + 1) - R E 3 n := by
  have h := congrArg (coeff (n + 1)) (key_identity E)
  rw [coeff_one_sub_X_mul, map_sub, map_add, map_sub, coeff_one_sub_X_mul, mul_assoc,
    coeff_three_mul, coeff_three_mul, coeff_U_sq, coeff_UD] at h
  rw [R, R, h]
  have := coeff_D_sq_nonneg E (n + 1)
  have := coeff_D_cube_le E (n + 1)
  have := coeff_D_cube_nonneg E n
  push_cast
  linarith

lemma coeff_G (n : ℕ) : coeff n (G E) = 1 - eps E n := by
  simp [G, U, coeff_D]

lemma coeff_G' (n : ℕ) : coeff n (G E) = if n ∈ E then 0 else 1 := by
  rw [coeff_G, eps]; split_ifs <;> norm_num

/-- The power-series definition is the count of ordered triples: `R_{A,3}(N)` is the number of
`((i, c), (a, b))` with `i + c = N`, `a + b = i` and `a, b, c ∉ E`. -/
theorem R_three_eq_card (N : ℕ) :
    R E 3 N = ((((antidiagonal N).sigma fun p => antidiagonal p.1)).filter
      (fun x => x.2.1 ∉ E ∧ x.2.2 ∉ E ∧ x.1.2 ∉ E)).card := by
  rw [R, pow_succ, sq, coeff_mul, Finset.card_filter, Nat.cast_sum, Finset.sum_sigma]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [coeff_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun q _ => ?_
  simp only [coeff_G']
  split_ifs <;> simp_all

lemma coeff_G_nonneg (n : ℕ) : 0 ≤ coeff n (G E) := by
  rw [coeff_G]; linarith [eps_le_one E n]

lemma coeff_G_pow_nonneg (k n : ℕ) : 0 ≤ coeff n (G E ^ k) := by
  induction k generalizing n with
  | zero => rw [pow_zero, coeff_one]; split_ifs <;> norm_num
  | succ k ih =>
    rw [pow_succ, coeff_mul]
    exact Finset.sum_nonneg fun p _ => mul_nonneg (ih _) (coeff_G_nonneg E _)

lemma coeff_zero_G_pow (h0 : 0 ∉ E) (k : ℕ) : coeff 0 (G E ^ k) = 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, coeff_mul, Finset.Nat.antidiagonal_zero, Finset.sum_singleton, ih, coeff_G]
    simp [eps, h0]

/-- A product of a series with positive coefficients and one with nonnegative coefficients and
constant term `1` has positive coefficients. -/
lemma coeff_pos_mul {F H : ℤ⟦X⟧} (hF : ∀ N, 0 < coeff N F) (hH : ∀ N, 0 ≤ coeff N H)
    (h1 : coeff 0 H = 1) (n : ℕ) : 0 < coeff n (F * H) := by
  rw [coeff_mul]
  have hmem : (n, 0) ∈ antidiagonal n := by simp
  have := Finset.single_le_sum (s := antidiagonal n) (f := fun p => coeff p.1 F * coeff p.2 H)
    (fun p _ => mul_nonneg (hF _).le (hH _)) hmem
  simp only [h1, mul_one] at this
  linarith [hF n]

/-- From `h = 3` to every `h ≥ 3`: `(1 - X) G^h = ((1 - X) G³) G^(h-3)`. -/
theorem strictMono_of_three (h0 : 0 ∉ E) (h3 : ∀ n, R E 3 n < R E 3 (n + 1)) (h : ℕ)
    (hh : 3 ≤ h) (n : ℕ) : R E h n < R E h (n + 1) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hh
  -- every coefficient of `F = (1 - X) G³` is positive
  have hF : ∀ N, 0 < coeff N ((1 - X) * G E ^ 3) := by
    intro N
    cases N with
    | zero => rw [coeff_zero_one_sub_X_mul, coeff_zero_G_pow E h0]; norm_num
    | succ N => rw [coeff_one_sub_X_mul]; have := h3 N; rw [R, R] at this; linarith
  have e : (1 - X) * G E ^ (3 + k) = ((1 - X) * G E ^ 3) * G E ^ k := by ring
  have key := coeff_pos_mul hF (coeff_G_pow_nonneg E k) (coeff_zero_G_pow E h0 k) (n + 1)
  rw [← e, coeff_one_sub_X_mul] at key
  rw [R, R]; linarith

end SandorYang
