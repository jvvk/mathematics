import Mathlib

/-!
# Half a window: the sequence and the window identity (Lemma 1)

`a 1 = 1`, `a n = a (n - 1)` for even `n`, and `a n = a (n - 1) - a ((n - 1) / 2) / n` for odd
`n ≥ 3` (`a 0 = 0` is a placeholder). The window of `n` is `W n = [⌈n/2⌉, n) = Ico ((n + 1) / 2) n`.
* `window`: `n a n = 1 + ∑_{k ∈ W n} a k` for `n ≥ 1`;
* `a_pos`, `one_le_c`: `a n > 0` and `n a n ≥ 1` for `n ≥ 1`.
-/

open Finset

namespace WindowSeq

/-- The sequence of MSE question 4748129. -/
noncomputable def a : ℕ → ℝ
  | 0 => 0
  | 1 => 1
  | (k + 2) => if (k + 2) % 2 = 0 then a (k + 1) else a (k + 1) - a ((k + 1) / 2) / (k + 2)

/-- The window `W n = {k : n/2 ≤ k < n}`. -/
def W (n : ℕ) : Finset ℕ := Ico ((n + 1) / 2) n

lemma a_succ_succ (k : ℕ) :
    a (k + 2) = if (k + 2) % 2 = 0 then a (k + 1) else a (k + 1) - a ((k + 1) / 2) / (k + 2) := by
  rw [a]

/-- Lemma 1 (the window identity). -/
theorem window (n : ℕ) (hn : 1 ≤ n) : (n : ℝ) * a n = 1 + ∑ k ∈ W n, a k := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  induction k with
  | zero => simp [W, a]
  | succ k ih =>
    rw [show 1 + (k + 1) = k + 2 by ring, a_succ_succ, W]
    have ih := ih (by omega)
    rw [show 1 + k = k + 1 by ring, W] at ih
    rcases Nat.even_or_odd k with ⟨t, rfl⟩ | ⟨t, rfl⟩
    · -- `k + 2 = 2t + 2` even: the window gains `k + 1` and keeps its bottom
      have hm : (t + t + 2 + 1) / 2 = (t + t + 1 + 1) / 2 := by omega
      rw [if_pos (show (t + t + 2) % 2 = 0 by omega), hm, Finset.sum_Ico_succ_top (by omega)]
      push_cast at ih ⊢
      linarith
    · -- `k + 2 = 2t + 3` odd: the window gains `k + 1` and loses its bottom `t + 1`
      have hm : (2 * t + 1 + 2 + 1) / 2 = (2 * t + 1 + 1 + 1) / 2 + 1 := by omega
      have hb : (2 * t + 1 + 1 + 1) / 2 = t + 1 := by omega
      have hd : (2 * t + 1 + 1) / 2 = t + 1 := by omega
      rw [if_neg (by omega), hm, hb, hd, Finset.sum_Ico_succ_top (by omega)]
      rw [hb, Finset.sum_eq_sum_Ico_succ_bot (by omega)] at ih
      push_cast at ih ⊢
      have h2 : (2 * (t : ℝ) + 1 + 2) ≠ 0 := by positivity
      rw [mul_sub, mul_div_cancel₀ _ h2]
      linarith

lemma mem_W {n k : ℕ} (hk : k ∈ W n) : (n + 1) / 2 ≤ k ∧ k < n := Finset.mem_Ico.1 hk

/-- `a n > 0` for `n ≥ 1`. -/
theorem a_pos (n : ℕ) (hn : 1 ≤ n) : 0 < a n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    have hsum : 0 ≤ ∑ k ∈ W n, a k := Finset.sum_nonneg fun k hk => by
      obtain ⟨h1, h2⟩ := mem_W hk
      exact (ih k h2 (by omega)).le
    have hw := window n hn
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
    by_contra h
    have : (n : ℝ) * a n ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hnpos.le (not_lt.1 h)
    linarith

/-- `c n = n a n`. -/
noncomputable def c (n : ℕ) : ℝ := n * a n

theorem one_le_c (n : ℕ) (hn : 1 ≤ n) : 1 ≤ c n := by
  rw [c, window n hn]
  have : 0 ≤ ∑ k ∈ W n, a k := Finset.sum_nonneg fun k hk => by
    obtain ⟨h1, h2⟩ := mem_W hk
    exact (a_pos k (by omega)).le
  linarith

/-- The identity in terms of `c`: `c n = 1 + ∑_{k ∈ W n} c k / k`. -/
theorem window_c (n : ℕ) (hn : 1 ≤ n) : c n = 1 + ∑ k ∈ W n, c k / k := by
  rw [c, window n hn]
  congr 1
  refine Finset.sum_congr rfl fun k hk => ?_
  obtain ⟨h1, h2⟩ := mem_W hk
  have : (k : ℝ) ≠ 0 := by have : 1 ≤ k := by omega
                           positivity
  rw [c]; field_simp

end WindowSeq
