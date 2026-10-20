import LeanProofs.Phyllotaxis.PassBalance

/-!
# Cyclic sweep and the step-one alternation

Item (d) of `open-questions/sunflower-phyllotaxis/PROOF_prop2.md` and the alternation step of the
`N = 1`
argument (`PROOF_ratio_law.md`, item (b)).

Downs never pass each other, so they keep a cyclic labelling `0, ..., m - 1` (labels in `ZMod m`).
Beside
the gaps of `PassBalance`, the state records `r i`, the label of the first down to the right of up
`i`.
The downs of gap `i` are then `r i, r i + 1, ..., r i + g i - 1`, which is consistent exactly when
`r (i + 1) = r i + g i` (`Consistent`). A pass by up `k` moves the last down of gap `k - 1`, label
`r k - 1`, to the front of gap `k`, so `r k` drops by one and no other `r i` changes.

* `labels_eq`: after a run `s`, `r i = r0 i - count i`.
* `consistent_run`: every run preserves consistency (the labelling stays a cyclic order).
* `sweep`: the `p`-th pass of up `u` passes down `r0 u - p`: an up meets the downs in decreasing
  cyclic
  order. This is the hypothesis `du k ≡ αu - k` of `Prop2.prop2`.
* `alternation_gap`: for two ups passing strictly alternately (first `a`), the gap after `a` is
  `g0 + count a - count b ∈ {g0, g0 + 1}`; with `g0 = 1` it never empties (step one: `{1, 2}`).
-/

namespace Phyllotaxis

open Finset

variable {n m : ℕ} [NeZero n]

/-- One pass by up `k`: the first-down label of `k` drops by one. -/
def rstep (r : Fin n → ZMod m) (k : Fin n) : Fin n → ZMod m :=
  fun i => r i - (if k = i then 1 else 0)

/-- Labels after a run of passes. -/
def labels (r0 : Fin n → ZMod m) (s : List (Fin n)) : Fin n → ZMod m := s.foldl rstep r0

omit [NeZero n] in
theorem labels_eq (r0 : Fin n → ZMod m) (s : List (Fin n)) (i : Fin n) :
    labels r0 s i = r0 i - (s.count i : ZMod m) := by
  induction s generalizing r0 with
  | nil => simp [labels]
  | cons k s ih =>
    have h := ih (rstep r0 k)
    simp only [labels, List.foldl_cons] at h ⊢
    rw [h]
    simp only [rstep, List.count_cons, beq_iff_eq]
    split_ifs <;> push_cast <;> ring

/-- The labelling is consistent with the gaps: gap `i` holds labels `r i, ..., r (i + 1) - 1`. -/
def Consistent (g : Fin n → ℤ) (r : Fin n → ZMod m) : Prop := ∀ i, r (i + 1) = r i + (g i : ZMod m)

/-- Runs preserve consistency. -/
theorem consistent_run {g0 : Fin n → ℤ} {r0 : Fin n → ZMod m} (h : Consistent g0 r0)
    (s : List (Fin n)) : Consistent (gaps g0 s) (labels r0 s) := by
  intro i
  rw [labels_eq, labels_eq, gaps_eq, h i]
  push_cast
  ring

omit [NeZero n] in
/-- **Cyclic sweep.** If the `j`-th entry of the run is a pass by `u`, and it is `u`'s `p`-th pass,
it
moves the down labelled `r0 u - p`. -/
theorem sweep (r0 : Fin n → ZMod m) (s : List (Fin n)) (j : ℕ) (hj : j < s.length) :
    labels r0 (s.take j) s[j] - 1 = r0 s[j] - (((s.take (j + 1)).count s[j] : ℕ) : ZMod m) := by
  rw [labels_eq, List.take_add_one, List.count_append]
  simp [List.getElem?_eq_getElem hj]
  ring

/-- Two ups passing strictly alternately, `a` first, for `2 j` or `2 j + 1` passes. -/
def alt (a b : Fin n) : ℕ → List (Fin n)
  | 0 => []
  | 1 => [a]
  | j + 2 => a :: b :: alt a b j

omit [NeZero n] in
theorem alt_count {a b : Fin n} (hab : a ≠ b) (j : ℕ) :
    ((alt a b j).count a : ℤ) - (alt a b j).count b = (j % 2 : ℕ) := by
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    match j, ih with
    | 0, _ => simp [alt]
    | 1, _ => simp [alt, hab]
    | j + 2, ih =>
      have := ih j (by omega)
      simp only [alt, List.count_cons, beq_iff_eq, hab, hab.symm, ite_false]
      rw [show (j + 2) % 2 = j % 2 by omega]
      push_cast at this ⊢
      linarith

/-- **Alternation.** Gap `a` (the downs right after `a`, before `b = a + 1`) after any alternating
run is
`g0 a + (0 or 1)`. In the step-one `(2,2)` phase (`g0 a = 1`) it is `1` or `2`, never `0`. -/
theorem alternation_gap {a : Fin n} (hab : a ≠ a + 1) (g0 : Fin n → ℤ) (j : ℕ) :
    gaps g0 (alt a (a + 1) j) a = g0 a + (j % 2 : ℕ) := by
  rw [gaps_eq, ← alt_count hab]
  ring

end Phyllotaxis
