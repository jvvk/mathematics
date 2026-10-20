import Mathlib

/-!
# Pass balance in rhombic phases of disk stacking

Combinatorial lemma behind Proposition 2 of the sunflower-phyllotaxis note
(`open-questions/sunflower-phyllotaxis/PROOF_prop2.md`, items (c) and (e)).

A front has `n` up vectors, kept in a fixed cyclic order, and some down vectors between them.
Gap `i` holds the downs between up `i` and up `i + 1` (indices in `Fin n`, cyclic).
A rhombic step is a *pass*: up `k` moves one place to the left, past one down, so that down moves
from gap `k - 1` to gap `k`. A run is a list of passes.

* `gaps_eq`: after a run `s`, gap `i` equals `g0 i + count i - count (i + 1)`.
* `sum_gaps`: the total number of downs is conserved.
* `pass_balance`: if the gaps are nonnegative at the start and at the end, any two ups have made
  numbers of passes differing by at most the number of downs `m = ∑ g0`.
* `pass_lag`: hence `|n * P u - t| ≤ n * m` for every up `u`, where `t` is the number of passes.
-/

namespace Phyllotaxis

open Finset Fin.CommRing

variable {n : ℕ} [NeZero n]

/-- One pass by up `k`: one down moves from gap `k - 1` to gap `k`. -/
def step (g : Fin n → ℤ) (k : Fin n) : Fin n → ℤ :=
  fun i => g i + (if k = i then 1 else 0) - (if k = i + 1 then 1 else 0)

/-- Gaps after a run of passes. -/
def gaps (g0 : Fin n → ℤ) (s : List (Fin n)) : Fin n → ℤ := s.foldl step g0

theorem gaps_eq (g0 : Fin n → ℤ) (s : List (Fin n)) (i : Fin n) :
    gaps g0 s i = g0 i + (s.count i : ℤ) - (s.count (i + 1) : ℤ) := by
  induction s generalizing g0 with
  | nil => simp [gaps]
  | cons k s ih =>
    have h := ih (step g0 k)
    simp only [gaps, List.foldl_cons] at h ⊢
    rw [h]
    clear h ih
    simp only [step, List.count_cons, beq_iff_eq]
    split_ifs <;> push_cast <;> ring

theorem sum_gaps (g0 : Fin n → ℤ) (s : List (Fin n)) :
    ∑ i, gaps g0 s i = ∑ i, g0 i := by
  simp only [gaps_eq, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  have h : ∑ i : Fin n, (s.count (i + 1) : ℤ) = ∑ i : Fin n, (s.count i : ℤ) :=
    Fintype.sum_equiv (Equiv.addRight 1) _ _ (fun _ => rfl)
  rw [h]
  ring

theorem tele (g0 : Fin n → ℤ) (s : List (Fin n)) (a : ℕ) :
    (s.count (a : Fin n) : ℤ) - s.count ((a + 1 : ℕ) : Fin n) =
      gaps g0 s (a : Fin n) - g0 (a : Fin n) := by
  rw [gaps_eq]
  push_cast
  ring

theorem count_sub_eq_sum (g0 : Fin n → ℤ) (s : List (Fin n)) (j d : ℕ) :
    (s.count (j : Fin n) : ℤ) - s.count ((j + d : ℕ) : Fin n) =
      ∑ l ∈ range d, (gaps g0 s ((j + l : ℕ) : Fin n) - g0 ((j + l : ℕ) : Fin n)) := by
  have h := Finset.sum_range_sub' (fun l => (s.count ((j + l : ℕ) : Fin n) : ℤ)) d
  simp only [add_zero] at h
  rw [← h]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [show j + (l + 1) = j + l + 1 by ring]
  exact tele g0 s (j + l)

theorem sum_window (G : Fin n → ℤ) (hG : ∀ i, 0 ≤ G i) (j d : ℕ) (hjd : j + d ≤ n) :
    0 ≤ ∑ l ∈ range d, G ((j + l : ℕ) : Fin n) ∧
      ∑ l ∈ range d, G ((j + l : ℕ) : Fin n) ≤ ∑ i, G i := by
  refine ⟨Finset.sum_nonneg fun l _ => hG _, ?_⟩
  have hinj : ∀ a ∈ range d, ∀ b ∈ range d,
      ((j + a : ℕ) : Fin n) = ((j + b : ℕ) : Fin n) → a = b := by
    intro a ha b hb hab
    rw [Finset.mem_range] at ha hb
    have h := congrArg Fin.val hab
    rw [Fin.val_cast_of_lt (by omega), Fin.val_cast_of_lt (by omega)] at h
    omega
  rw [← Finset.sum_image hinj]
  exact Finset.sum_le_univ_sum_of_nonneg hG

/-- **Pass balance.** Two ups never differ in their number of passes by more than the number of
downs. Applied to every prefix of a run, this holds at every time. -/
theorem pass_balance (g0 : Fin n → ℤ) (s : List (Fin n))
    (h0 : ∀ i, 0 ≤ g0 i) (hs : ∀ i, 0 ≤ gaps g0 s i) (j k : Fin n) :
    |(s.count j : ℤ) - s.count k| ≤ ∑ i, g0 i := by
  wlog hjk : j.val ≤ k.val generalizing j k
  · rw [abs_sub_comm]
    exact this k j (by omega)
  have hk := k.isLt
  obtain ⟨hA0, hA⟩ := sum_window (gaps g0 s) hs j.val (k.val - j.val) (by omega)
  obtain ⟨hB0, hB⟩ := sum_window g0 h0 j.val (k.val - j.val) (by omega)
  have htot := sum_gaps g0 s
  have key := count_sub_eq_sum g0 s j.val (k.val - j.val)
  rw [show j.val + (k.val - j.val) = k.val by omega, Fin.cast_val_eq_self,
    Fin.cast_val_eq_self] at key
  rw [key, Finset.sum_sub_distrib, abs_le]
  constructor <;> linarith

omit [NeZero n] in
theorem sum_count_univ (s : List (Fin n)) :
    ∑ v : Fin n, (s.count v : ℤ) = s.length := by
  rw [← Nat.cast_sum, ← List.sum_toFinset_count_eq_length]
  norm_cast
  symm
  refine Finset.sum_subset (Finset.subset_univ _) fun v _ hv => ?_
  exact List.count_eq_zero_of_not_mem (by simpa using hv)

/-- **Bounded lag.** After `t = s.length` passes, every up has made between `t/n - m` and
`t/n + m` passes, so the `k`-th passes of any two ups are at most `2 n m` steps apart. -/
theorem pass_lag (g0 : Fin n → ℤ) (s : List (Fin n))
    (h0 : ∀ i, 0 ≤ g0 i) (hs : ∀ i, 0 ≤ gaps g0 s i) (u : Fin n) :
    |(n : ℤ) * s.count u - s.length| ≤ (n : ℤ) * ∑ i, g0 i := by
  have hsum : (n : ℤ) * s.count u - s.length = ∑ v : Fin n, ((s.count u : ℤ) - s.count v) := by
    rw [← sum_count_univ s, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
  rw [hsum]
  calc |∑ v : Fin n, ((s.count u : ℤ) - s.count v)|
      ≤ ∑ v : Fin n, |(s.count u : ℤ) - s.count v| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _v : Fin n, ∑ i, g0 i := Finset.sum_le_sum fun v _ => pass_balance g0 s h0 hs u v
    _ = (n : ℤ) * ∑ i, g0 i := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

end Phyllotaxis
