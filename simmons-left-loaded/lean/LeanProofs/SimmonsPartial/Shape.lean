import Mathlib

/-!
# Step (6), abstractly: a sequence that falls then rises to a negative end

Let `a : ℕ → ℤ` on `[1, q]` satisfy
* (step) for `1 ≤ i` with `i + 1 < q`: `a i ≤ a (i + 1)` forces `a (i + 1) < a (i + 2)`
  (once the differences stop being negative they stay positive);
* (last) `a q < 0`;
* (total) `Σ_{i=1}^{q} a i = 0`.

Then `a` falls strictly while it falls and rises after, so its values on `[1, q]` are a nonnegative block
followed by a negative block (`neg_persists`), and every proper partial sum is positive (`partial_pos`):
if `a (k + 1) < 0` the tail `a (k + 1), ..., a q` is negative and sums to `- Σ_{i ≤ k} a i`; otherwise
`a 1, ..., a (k + 1) ≥ 0`, and `a 1 > a 2` (a first rise would carry `a` up to `a q < 0`), so `a 1 > 0`.
-/

namespace SimmonsPartial

open Finset

section Shape

variable (a : ℕ → ℤ) (q : ℕ)

/-- Once a difference is `≥ 0`, the sequence rises to `a q`. -/
lemma up (hstep : ∀ i, 1 ≤ i → i + 1 < q → a i ≤ a (i + 1) → a (i + 1) < a (i + 1 + 1))
    {l : ℕ} (hl : 1 ≤ l) (hD : a l ≤ a (l + 1)) : ∀ j, l ≤ j → j ≤ q → a j ≤ a q := by
  have hinc : ∀ i, l ≤ i → i < q → a i ≤ a (i + 1) := by
    intro i hi
    induction i, hi using Nat.le_induction with
    | base => exact fun _ => hD
    | succ i hi ih => exact fun h => (hstep i (by omega) h (ih (by omega))).le
  have key : ∀ t j, j + t = q → l ≤ j → a j ≤ a q := by
    intro t
    induction t with
    | zero => intro j hj _; rw [← hj, Nat.add_zero]
    | succ t ih => intro j hj hl'; exact (hinc j hl' (by omega)).trans (ih (j + 1) (by omega) (by omega))
  exact fun j hl' hj => key (q - j) j (by omega) hl'

/-- A strictly falling stretch ends below its start. -/
lemma down {s t : ℕ} (h : ∀ i, s ≤ i → i < t → a (i + 1) < a i) : ∀ j, s ≤ j → j ≤ t → a j ≤ a s := by
  intro j hj
  induction j, hj using Nat.le_induction with
  | base => exact fun _ => le_rfl
  | succ j hj ih => exact fun hjt => (h j hj (by omega)).le.trans (ih (by omega))

/-- **One sign change.** On `[1, q]`, once `a` is negative it stays negative. -/
theorem neg_persists (hstep : ∀ i, 1 ≤ i → i + 1 < q → a i ≤ a (i + 1) → a (i + 1) < a (i + 1 + 1))
    (hlast : a q < 0) {i j : ℕ} (hi : 1 ≤ i) (hij : i ≤ j) (hj : j ≤ q) (h : a i < 0) : a j < 0 := by
  by_cases hex : ∃ l, i ≤ l ∧ l < j ∧ a l ≤ a (l + 1)
  · obtain ⟨l, hil, hlj, hl⟩ := hex
    exact (up a q hstep (by omega) hl j (by omega) hj).trans_lt hlast
  · push Not at hex
    exact (down a (fun l h1 h2 => hex l h1 h2) j hij le_rfl).trans_lt h

/-- **Positive partial sums.** `Σ_{i=1}^{k} a i > 0` for `1 ≤ k < q`. -/
theorem partial_pos (hstep : ∀ i, 1 ≤ i → i + 1 < q → a i ≤ a (i + 1) → a (i + 1) < a (i + 1 + 1))
    (hlast : a q < 0) (htot : ∑ i ∈ Icc 1 q, a i = 0) {k : ℕ} (hk1 : 1 ≤ k) (hk : k < q) :
    0 < ∑ i ∈ Icc 1 k, a i := by
  rcases lt_or_ge (a (k + 1)) 0 with hneg | hnn
  · -- the tail `a (k+1), ..., a q` is negative
    have hdec : ∀ j, k + 1 ≤ j → j ≤ q → ∑ i ∈ Icc 1 j, a i < ∑ i ∈ Icc 1 k, a i := by
      intro j hj
      induction j, hj using Nat.le_induction with
      | base => intro _; rw [sum_Icc_succ_top (by omega)]; linarith
      | succ j hj ih =>
        intro hjq
        rw [sum_Icc_succ_top (by omega)]
        have := neg_persists a q hstep hlast (by omega) (show k + 1 ≤ j + 1 by omega) hjq hneg
        linarith [ih (by omega)]
    have := hdec q (by omega) le_rfl
    rw [htot] at this; exact this
  · -- `a 1, ..., a (k+1)` are nonnegative and `a 1 > a 2`
    have hall : ∀ i, 1 ≤ i → i ≤ k + 1 → 0 ≤ a i := fun i h1 h2 => by
      by_contra hc; push Not at hc
      exact absurd (neg_persists a q hstep hlast h1 h2 (by omega) hc) (not_lt.2 hnn)
    have h12 : a 2 < a 1 := by
      by_contra hc; push Not at hc
      have := (up a q hstep le_rfl hc (k + 1) (by omega) (by omega)).trans_lt hlast
      exact absurd this (not_lt.2 hnn)
    have ha1 : 0 < a 1 := lt_of_le_of_lt (hall 2 (by omega) (by omega)) h12
    have hge : ∀ j, 1 ≤ j → j ≤ k → a 1 ≤ ∑ i ∈ Icc 1 j, a i := by
      intro j hj
      induction j, hj using Nat.le_induction with
      | base => intro _; simp
      | succ j hj ih =>
        intro hjk
        rw [sum_Icc_succ_top (by omega)]
        linarith [ih (by omega), hall (j + 1) (by omega) (by omega)]
    exact ha1.trans_le (hge k hk1 le_rfl)

end Shape

end SimmonsPartial
