/-
  Hofstadter–Conway comparison (MathOverflow q/366772), formalization of
  "The Hofstadter–Conway sequence dominates its alternating companion".

  Basic objects: the two sequences, and binary words encoded by their prefix-count functions.
-/
import Mathlib.Tactic

namespace HofConway

/-- The Hofstadter–Conway \$10,000 sequence (OEIS A004001):
    `c 1 = c 2 = 1`, `c n = c (c (n-1)) + c (n - c (n-1))`.
    A call outside `[1, n-1]` returns `0`; the block proposition shows this never happens. -/
def c : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | 2 => 1
  | n + 3 =>
    let x := c (n + 2)
    if _h : 1 ≤ x ∧ x ≤ n + 2 then c x + c (n + 3 - x) else 0
termination_by n => n
decreasing_by all_goals omega

/-- Alkan's companion sequence (OEIS A287422):
    `s 1 = s 2 = 1`, `s n = n - s (s (n-1)) - s (n - s (n-1))`.
    Same guard as `c`; the subtraction is truncated, and the block proposition shows it never truncates. -/
def s : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | 2 => 1
  | n + 3 =>
    let x := s (n + 2)
    if _h : 1 ≤ x ∧ x ≤ n + 2 then n + 3 - s x - s (n + 3 - x) else 0
termination_by n => n
decreasing_by all_goals omega

/-- `P` is the prefix-count function of a Dyck word of length `L`: `P 0 = 0`, increments `0` or `1`,
    constant from `L` on (so the letter at `L + 1` is `0`), height `2 P i - i ≥ 0`, and `2 P L = L`. -/
structure Dyck (L : ℕ) (P : ℕ → ℕ) : Prop where
  zero : P 0 = 0
  step : ∀ i, P i ≤ P (i + 1) ∧ P (i + 1) ≤ P i + 1
  tail : ∀ i, L ≤ i → P i = P L
  half : ∀ i, i ≤ L → i ≤ 2 * P i
  total : 2 * P L = L

/-- Irreducible: the height is positive strictly inside the word. -/
def Irred (L : ℕ) (P : ℕ → ℕ) : Prop := ∀ i, 0 < i → i < L → i < 2 * P i

/-- Symmetric under reversal and complement, in the prefix form (2.1): `P (L - i) = m - i + P i`. -/
def Symm (L : ℕ) (P : ℕ → ℕ) : Prop := ∀ i, i ≤ L → P (L - i) + i = L / 2 + P i

/-- The letter at position `i ≥ 1`. -/
def letter (P : ℕ → ℕ) (i : ℕ) : ℕ := P i - P (i - 1)

namespace Dyck

variable {L : ℕ} {P : ℕ → ℕ}

theorem mono (hD : Dyck L P) {i k : ℕ} (h : i ≤ k) : P i ≤ P k := by
  induction k with
  | zero => simp at h; subst h; rfl
  | succ k ih =>
    rcases Nat.eq_or_lt_of_le h with h | h
    · rw [h]
    · exact le_trans (ih (by omega)) (hD.step k).1

theorem le_self (hD : Dyck L P) (i : ℕ) : P i ≤ i := by
  induction i with
  | zero => simp [hD.zero]
  | succ i ih => have := (hD.step i).2; omega

theorem le_top (hD : Dyck L P) (i : ℕ) : P i ≤ P L := by
  rcases le_total i L with h | h
  · exact hD.mono h
  · rw [hD.tail i h]

theorem succ_cases (hD : Dyck L P) (i : ℕ) : P (i + 1) = P i ∨ P (i + 1) = P i + 1 := by
  have := hD.step i; omega

end Dyck

end HofConway

