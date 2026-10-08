import AlternatingSum.Leibniz
import Mathlib.Tactic.FieldSimp

/-!
  The sum `L(u,a,b,n)` exactly as in MathOverflow question 498232, and Step 1 of the paper:
  grouping its factorials into binomial coefficients, which (with Step 3) gives
  `L = (u+ν)!² / ν! · Σ_{k,ℓ} (-1)^k C(s,k) C(j,a-k) c_{s,j}` with `s = k+ℓ`, `j = a+b-s`.
-/

namespace Abdesselam

open Finset Nat

/-- The summation range of the question: `0 ≤ i ≤ n`, `0 ≤ k ≤ a`, `0 ≤ ℓ ≤ b` and the two
factorial arguments `a+b-k-ℓ-i` and `k+ℓ-n+i` nonnegative (every other argument is then
nonnegative automatically). -/
def inRange (a b n i k l : ℕ) : Prop := n ≤ i + k + l ∧ i + k + l ≤ a + b

instance (a b n i k l : ℕ) : Decidable (inRange a b n i k l) := by
  unfold inRange; infer_instance

/-- The summand of the question, without the prefactor `(u+a+b-n)!`. The factorial argument
`k+ℓ-n+i` of the question is written `k+ℓ+i-n` so that natural subtraction does not truncate. -/
def term (u a b n i k l : ℕ) : ℚ :=
  (-1) ^ k * (((u + a + b - i) ! * (k + l) ! * (a + b - k - l) ! * (u + a + b - k - l) ! : ℕ) : ℚ) /
    ((i ! * (n - i) ! * k ! * (a - k) ! * l ! * (b - l) ! * (a + b - k - l - i) ! *
      (k + l + i - n) ! * (u + a + b - k - l - i) ! : ℕ) : ℚ)

/-- Abdesselam's sum `L(u,a,b,n)`. -/
def L (u a b n : ℕ) : ℚ :=
  ((u + a + b - n) ! : ℚ) * ∑ i ∈ range (n + 1), ∑ k ∈ range (a + 1), ∑ l ∈ range (b + 1),
    if inRange a b n i k l then term u a b n i k l else 0

/-- The alternating form of `c_{s,j}` (Step 3), with `ν` and `u` fixed. -/
def c (u ν s j : ℕ) : ℚ :=
  ∑ p ∈ range (ν + 1), (-1 : ℚ) ^ p * (ν.choose p : ℚ) * ((u + ν - p + s).choose s : ℚ) *
    ((u + ν - p + j).choose j : ℚ)

/-- Step 1, one term: the factorials regroup into five binomial coefficients. -/
theorem term_eq (u a b n i k l : ℕ) (hi : i ≤ n) (hk : k ≤ a) (hl : l ≤ b)
    (h : inRange a b n i k l) :
    ((u + a + b - n) ! : ℚ) * term u a b n i k l =
      ((u + a + b - n) ! : ℚ) ^ 2 / ((a + b - n) ! : ℚ) *
        ((-1) ^ k * ((k + l).choose k : ℚ) * ((a + b - k - l).choose (a - k) : ℚ)) *
        (((a + b - n).choose (a + b - k - l - i) : ℚ) * ((u + (a + b - k - l)).choose i : ℚ) *
          ((u + (k + l) + (a + b - k - l) - i).choose (n - i) : ℚ)) := by
  obtain ⟨h1, h2⟩ := h
  rw [Nat.cast_choose ℚ (by omega : k ≤ k + l), Nat.cast_choose ℚ (by omega : a - k ≤ a + b - k - l),
    Nat.cast_choose ℚ (by omega : a + b - k - l - i ≤ a + b - n),
    Nat.cast_choose ℚ (by omega : i ≤ u + (a + b - k - l)),
    Nat.cast_choose ℚ (by omega : n - i ≤ u + (k + l) + (a + b - k - l) - i)]
  have e1 : k + l - k = l := by omega
  have e2 : a + b - k - l - (a - k) = b - l := by omega
  have e3 : a + b - n - (a + b - k - l - i) = k + l + i - n := by omega
  have e4 : u + (a + b - k - l) - i = u + a + b - k - l - i := by omega
  have e5 : u + (k + l) + (a + b - k - l) - i = u + a + b - i := by omega
  have e6 : u + a + b - i - (n - i) = u + a + b - n := by omega
  have e7 : u + (a + b - k - l) = u + a + b - k - l := by omega
  rw [e1, e2, e3, e4, e5, e6, e7]
  simp only [term, Nat.cast_mul]
  field_simp

/-- Steps 1 and 3: `L` as a double sum over `k, ℓ` of the alternating sign, two binomials and
`c_{k+ℓ, a+b-k-ℓ}`. -/
theorem step1 (u a b n : ℕ) (hn : n ≤ a + b) :
    L u a b n = ((u + a + b - n) ! : ℚ) ^ 2 / ((a + b - n) ! : ℚ) *
      ∑ k ∈ range (a + 1), ∑ l ∈ range (b + 1),
        (-1) ^ k * ((k + l).choose k : ℚ) * ((a + b - k - l).choose (a - k) : ℚ) *
          c u (a + b - n) (k + l) (a + b - k - l) := by
  have hswap : L u a b n = ∑ k ∈ range (a + 1), ∑ l ∈ range (b + 1), ∑ i ∈ range (n + 1),
      ((u + a + b - n) ! : ℚ) * (if inRange a b n i k l then term u a b n i k l else 0) := by
    rw [L, mul_sum]
    simp_rw [mul_sum]
    rw [sum_comm]
    exact sum_congr rfl fun _ _ ↦ sum_comm
  rw [hswap, mul_sum]
  refine sum_congr rfl fun k hk ↦ ?_
  rw [mul_sum]
  refine sum_congr rfl fun l hl ↦ ?_
  have hk := mem_range.1 hk
  have hl := mem_range.1 hl
  have hstep : ∀ i ∈ range (n + 1), ((u + a + b - n) ! : ℚ) *
      (if inRange a b n i k l then term u a b n i k l else 0) =
      ((u + a + b - n) ! : ℚ) ^ 2 / ((a + b - n) ! : ℚ) *
        ((-1) ^ k * ((k + l).choose k : ℚ) * ((a + b - k - l).choose (a - k) : ℚ)) *
        (if n ≤ i + (k + l) ∧ i ≤ a + b - k - l then
          ((a + b - n).choose (a + b - k - l - i) : ℚ) * ((u + (a + b - k - l)).choose i : ℚ) *
            ((u + (k + l) + (a + b - k - l) - i).choose (n - i) : ℚ) else 0) := by
    intro i hi
    have hi := mem_range.1 hi
    by_cases h : inRange a b n i k l
    · have h' : n ≤ i + (k + l) ∧ i ≤ a + b - k - l := by unfold inRange at h; omega
      rw [ite_eq_left h, ite_eq_left h', term_eq u a b n i k l (by omega) (by omega) (by omega) h]
    · have h' : ¬ (n ≤ i + (k + l) ∧ i ≤ a + b - k - l) := by unfold inRange at h; omega
      rw [ite_eq_right h, ite_eq_right h', mul_zero, mul_zero]
  rw [sum_congr rfl hstep, ← mul_sum,
    step3 u (a + b - n) (k + l) (a + b - k - l) n (by omega), c]
  ring

end Abdesselam
