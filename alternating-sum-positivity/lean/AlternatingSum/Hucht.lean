import AlternatingSum.Binomial
import Mathlib.Tactic.LinearCombination

/-!
  Hucht's form of Taylor's inner sums (his MathOverflow answer, equation (3)): with `c = a/2 + b`,
  `k = μ + ν ≤ c` and `j = c - k`,
  `Tinner = 2^b C(c,b) C(c,k) ₃F₂((1-b)/2, -b/2, -j; -c, -c; 1)`,
  and therefore the terminating ₃F₂ is positive whenever `μ + ν ≤ c`.
-/

namespace Abdesselam

open Finset Nat

/-- The rising factorial `(x)_t` over `ℚ`. -/
def qrise (x : ℚ) (t : ℕ) : ℚ := ∏ i ∈ range t, (x + i)

/-- Hucht's terminating series `₃F₂((1-b)/2, -b/2, -j; -c, -c; 1)`. -/
def F32 (b j c : ℕ) : ℚ :=
  ∑ t ∈ range (j + 1), qrise ((1 - b) / 2) t * qrise (-(b : ℚ) / 2) t * qrise (-(j : ℚ)) t /
    (qrise (-(c : ℚ)) t ^ 2 * (t ! : ℚ))

theorem qrise_neg_nat (N t : ℕ) (h : t ≤ N) :
    qrise (-(N : ℚ)) t = (-1) ^ t * (N ! : ℚ) / ((N - t) ! : ℚ) := by
  induction t with
  | zero => simp [qrise, div_self (by positivity : (N ! : ℚ) ≠ 0)]
  | succ t ih =>
    rw [qrise, prod_range_succ, ← qrise, ih (by omega)]
    have : N - t = (N - (t + 1)) + 1 := by omega
    rw [this, Nat.factorial_succ]
    push_cast [show t ≤ N by omega]
    field_simp
    rw [show ((N - (t + 1) : ℕ) : ℚ) = (N : ℚ) - t - 1 by push_cast [show t + 1 ≤ N by omega]; ring]
    ring

theorem qrise_neg_nat_zero (N t : ℕ) (h : N < t) : qrise (-(N : ℚ)) t = 0 := by
  rw [qrise]
  exact prod_eq_zero (mem_range.2 h) (by ring)

theorem qrise_half_mul (b t : ℕ) (h : 2 * t ≤ b) :
    qrise ((1 - b) / 2) t * qrise (-(b : ℚ) / 2) t * (((b - 2 * t) ! : ℚ) * 4 ^ t) = (b ! : ℚ) := by
  induction t with
  | zero => simp [qrise]
  | succ t ih =>
    have ih' := ih (by omega)
    rw [qrise, qrise, prod_range_succ, prod_range_succ, ← qrise, ← qrise]
    have e : b - 2 * t = (b - 2 * (t + 1)) + 1 + 1 := by omega
    rw [e, Nat.factorial_succ, Nat.factorial_succ] at ih'
    have hb : ((b - 2 * (t + 1) : ℕ) : ℚ) = (b : ℚ) - 2 * t - 2 := by
      push_cast [show 2 * (t + 1) ≤ b by omega]; ring
    push_cast at ih' ⊢
    rw [hb] at ih'
    linear_combination ih'

theorem qrise_half (b t : ℕ) (h : 2 * t ≤ b) :
    qrise ((1 - b) / 2) t * qrise (-(b : ℚ) / 2) t = (b ! : ℚ) / ((b - 2 * t) ! : ℚ) / 4 ^ t := by
  rw [← qrise_half_mul b t h]
  field_simp

theorem qrise_half_zero (b t : ℕ) (h : b < 2 * t) :
    qrise ((1 - b) / 2) t * qrise (-(b : ℚ) / 2) t = 0 := by
  rcases Nat.even_or_odd b with ⟨r, hr⟩ | ⟨r, hr⟩
  · refine mul_eq_zero_of_right _ (prod_eq_zero (i := r) (mem_range.2 (by omega)) ?_)
    rw [hr]; push_cast; ring
  · refine mul_eq_zero_of_left (prod_eq_zero (i := r) (mem_range.2 (by omega)) ?_) _
    rw [hr]; push_cast; ring

theorem neg_one_pow_sq (t : ℕ) : ((-1 : ℚ) ^ t) ^ 2 = 1 := by
  rw [← pow_mul, mul_comm, pow_mul]; simp

/-- One term of Hucht's series against the matching term of Taylor's sum (`d = b - t`). -/
theorem hucht_term (b c k t : ℕ) (hbc : b ≤ c) (hk : k ≤ c) (ht : 2 * t ≤ b) (htj : t ≤ c - k) :
    2 ^ b * (c.choose b : ℚ) * (c.choose k : ℚ) *
      (qrise ((1 - b) / 2) t * qrise (-(b : ℚ) / 2) t * qrise (-((c - k : ℕ) : ℚ)) t /
        (qrise (-(c : ℚ)) t ^ 2 * (t ! : ℚ))) =
    (-1) ^ t * 2 ^ (b - 2 * t) * ((b - t).choose (b - 2 * t) : ℚ) *
      ((c - t).choose (b - t) : ℚ) * ((c - t).choose k : ℚ) := by
  rw [qrise_half b t ht, qrise_neg_nat (c - k) t htj, qrise_neg_nat c t (by omega)]
  rw [Nat.cast_choose ℚ hbc, Nat.cast_choose ℚ hk, Nat.cast_choose ℚ (by omega : b - 2 * t ≤ b - t),
    Nat.cast_choose ℚ (by omega : b - t ≤ c - t), Nat.cast_choose ℚ (by omega : k ≤ c - t)]
  have e1 : b - t - (b - 2 * t) = t := by omega
  have e2 : c - t - (b - t) = c - b := by omega
  have e3 : c - t - k = c - k - t := by omega
  have h2 : (2 : ℚ) ^ b = 2 ^ (b - 2 * t) * 4 ^ t := by
    rw [show (4 : ℚ) = 2 ^ 2 by norm_num, ← pow_mul, ← pow_add]; congr 1; omega
  rw [e1, e2, e3, h2, div_pow, mul_pow, neg_one_pow_sq]
  field_simp

/-- **Hucht's identity:** for even `a` and `k = m + ν ≤ c = a/2 + b`, Taylor's inner sum is
`2^b C(c,b) C(c,k) ₃F₂((1-b)/2, -b/2, k-c; -c, -c; 1)`. -/
theorem hucht_identity (a b n m : ℕ) (hn : n ≤ a + b) (hk : m + (a + b - n) ≤ a / 2 + b) :
    Tinner a b n m = 2 ^ b * ((a / 2 + b).choose b : ℚ) *
      ((a / 2 + b).choose (m + (a + b - n)) : ℚ) *
      F32 b (a / 2 + b - (m + (a + b - n))) (a / 2 + b) := by
  set c := a / 2 + b with hc
  set k := m + (a + b - n) with hkdef
  set j := c - k with hj
  let Tt : ℕ → ℚ := fun t ↦ (-1) ^ t * 2 ^ (b - 2 * t) * ((b - t).choose (b - 2 * t) : ℚ) *
    ((c - t).choose (b - t) : ℚ) * ((c - t).choose k : ℚ)
  let H : ℕ → ℚ := fun t ↦ qrise ((1 - b) / 2) t * qrise (-(b : ℚ) / 2) t * qrise (-(j : ℚ)) t /
    (qrise (-(c : ℚ)) t ^ 2 * (t ! : ℚ))
  -- Taylor's sum, reindexed by `t = b - d`
  have hT : Tinner a b n m = ∑ t ∈ range (b / 2 + 1), Tt t := by
    rw [Tinner]
    refine sum_nbij' (fun d ↦ b - d) (fun t ↦ b - t) ?_ ?_ ?_ ?_ ?_
    · intro d hd; simp only [mem_Icc, mem_range] at hd ⊢; omega
    · intro t ht; simp only [mem_Icc, mem_range] at ht ⊢; omega
    · intro d hd; simp only [mem_Icc] at hd; omega
    · intro t ht; simp only [mem_range] at ht; omega
    · intro d hd
      simp only [mem_Icc] at hd
      simp only [Tt]
      rw [show b - (b - d) = d by omega, show b - 2 * (b - d) = 2 * d - b by omega,
        show c - (b - d) = a / 2 + d by omega, show m + a + b - n = k by omega]
  -- Hucht's series, cut at `t ≤ b/2` instead of `t ≤ j`
  have hH : F32 b j c = ∑ t ∈ range (b / 2 + 1), H t := by
    have hz1 : ∀ t, j < t → H t = 0 := fun t ht ↦ by
      simp only [H]; rw [qrise_neg_nat_zero j t ht, mul_zero, zero_div]
    have hz2 : ∀ t, b / 2 < t → H t = 0 := fun t ht ↦ by
      simp only [H]; rw [qrise_half_zero b t (by omega), zero_mul, zero_div]
    have h1 : F32 b j c = ∑ t ∈ range (b / 2 + j + 1), H t :=
      sum_subset (by intro t; simp only [mem_range]; omega) fun t _ ht ↦ hz1 t (by simp at ht; omega)
    have h2 : ∑ t ∈ range (b / 2 + 1), H t = ∑ t ∈ range (b / 2 + j + 1), H t :=
      sum_subset (by intro t; simp only [mem_range]; omega) fun t _ ht ↦ hz2 t (by simp at ht; omega)
    rw [h1, h2]
  rw [hT, hH, mul_sum]
  refine sum_congr rfl fun t ht ↦ ?_
  simp only [mem_range] at ht
  by_cases htj : t ≤ j
  · exact (hucht_term b c k t (by omega) hk (by omega) htj).symm
  · simp only [Tt, H]
    rw [qrise_neg_nat_zero j t (by omega), Nat.choose_eq_zero_of_lt (show c - t < k by omega)]
    simp

/-- **Hucht's guess, for `μ + ν ≤ c`:** the terminating ₃F₂ is positive. -/
theorem hucht_pos (a b n m : ℕ) (ha : Even a) (hn : n ≤ a + b) (hk : m + (a + b - n) ≤ a / 2 + b) :
    0 < F32 b (a / 2 + b - (m + (a + b - n))) (a / 2 + b) := by
  set k := m + (a + b - n) with hkdef
  have hpos : 0 < Tinner a b n m := by
    rw [← inner_eq_Tinner a b n m ha hn]
    have hL := (L_pos_iff 0 a b (a + b - k) (by omega)).2 ⟨ha, by obtain ⟨r, hr⟩ := ha; omega⟩
    rw [main 0 a b (a + b - k) (by omega), show a + b - (a + b - k) = k by omega, zero_add,
      pow_one] at hL
    exact pos_of_mul_pos_right hL (by positivity)
  rw [hucht_identity a b n m hn hk] at hpos
  have hpref : 0 < 2 ^ b * ((a / 2 + b).choose b : ℚ) * ((a / 2 + b).choose k : ℚ) := by
    have h1 : 0 < (a / 2 + b).choose b := Nat.choose_pos (by omega)
    have h2 : 0 < (a / 2 + b).choose k := Nat.choose_pos hk
    positivity
  exact pos_of_mul_pos_right hpos hpref.le

end Abdesselam
