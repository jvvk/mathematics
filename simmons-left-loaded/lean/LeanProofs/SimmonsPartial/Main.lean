import LeanProofs.SimmonsPartial.Total
import LeanProofs.SimmonsPartial.Ratio
import LeanProofs.SimmonsPartial.Shape

/-!
# Step (6): the Simmons partial sums (Fokkink-Papavassiliou-Pelekis, Conjecture 4.1)

For `n > 2m ≥ 2` the scaled gaps `A 1, ..., A q` satisfy the hypotheses of `partial_pos`: the step
condition is `d_step` through `A_succ`, the last value is `A q = - w n < 0`, and the total is `0`.
For `n = 2m` every `A i` with `i ≤ m + 1` vanishes, by the symmetry `w (m + i) = w (m - i)`.
-/

namespace SimmonsPartial

open Finset

lemma A_step {n m : ℕ} (hm : 1 ≤ m) (hn : 2 * m < n) :
    ∀ i, 1 ≤ i → i + 1 < n - m → A n m i ≤ A n m (i + 1) → A n m (i + 1) < A n m (i + 1 + 1) := by
  intro i hi hiq h
  have h1 := A_succ n m i
  have h2 := A_succ n m (i + 1)
  have := d_step hm hn hi hiq (by linarith)
  linarith

lemma A_last_neg {n m : ℕ} (hm : 1 ≤ m) (hn : 2 * m < n) : A n m (n - m) < 0 := by
  rw [A_last (by omega)]
  have := w_pos (n := n) (m := m) (j := n) (by omega) (by omega) le_rfl
  omega

/-- **Positive partial sums**, `n > 2m ≥ 2`, `1 ≤ k < q`. -/
theorem partial_sum_pos (n m k : ℕ) (hm : 1 ≤ m) (hn : 2 * m < n) (hk1 : 1 ≤ k) (hk : k < n - m) :
    0 < ∑ i ∈ Finset.Icc 1 k, A n m i :=
  partial_pos (A n m) (n - m) (A_step hm hn) (A_last_neg hm hn) (total hn.le (by omega)) hk1 hk

/-- **Sign pattern.** For `n > 2m ≥ 2`, once `A i < 0` (`i ≥ 1`), `A j < 0` for `i ≤ j ≤ q`. -/
theorem neg_persists_A (n m i j : ℕ) (hm : 1 ≤ m) (hn : 2 * m < n) (hi : 1 ≤ i) (hij : i ≤ j)
    (hj : j ≤ n - m) (h : A n m i < 0) : A n m j < 0 :=
  neg_persists (A n m) (n - m) (A_step hm hn) (A_last_neg hm hn) hi hij hj h

/-- **At most one sign change on `α_1, ..., α_m`** (from `+` to `-`): condition (L1). -/
theorem one_sign_change (n m i j : ℕ) (hm : 1 ≤ m) (hn : 2 * m < n) (hi : 1 ≤ i) (hij : i ≤ j)
    (hj : j ≤ m) (h : A n m i < 0) : A n m j < 0 :=
  neg_persists_A n m i j hm hn hi hij (by omega) h

/-- `w (m + i) = w (m - i)` when `n = 2m`. -/
lemma w_symm (m i : ℕ) (hi : i ≤ m) : w (2 * m) m (m + i) = w (2 * m) m (m - i) := by
  unfold w
  rw [show 2 * m - m = m by omega, show 2 * m - (m + i) = m - i by omega,
    show 2 * m - (m - i) = m + i by omega, Nat.choose_symm_of_eq_add (show 2 * m = (m + i) + (m - i) by omega)]
  ring

/-- **The symmetric case** `n = 2m`: `A i = 0` for `i ≤ m + 1`. -/
theorem A_symm_zero (m i : ℕ) (hi : i ≤ m + 1) : A (2 * m) m i = 0 := by
  have hd : ∀ i, i ≤ m → d (2 * m) m i = 0 := fun i hi => by simp [d, hi, w_symm m i hi]
  have key : ∀ t, t ≤ m + 1 → A (2 * m) m (m + 1 - t) = 0 := by
    intro t
    induction t with
    | zero => intro _; exact A_eq_zero (by omega) (by omega)
    | succ t ih =>
      intro ht
      have h := A_succ (2 * m) m (m - t)
      rw [hd _ (by omega), show m - t + 1 = m + 1 - t by omega, ih (by omega)] at h
      rw [show m + 1 - (t + 1) = m - t by omega]; linarith
  have := key (m + 1 - i) (by omega)
  rwa [show m + 1 - (m + 1 - i) = i by omega] at this

/-- **Conjecture 4.1** (Fokkink-Papavassiliou-Pelekis): for `n ≥ 2m ≥ 2` and `1 ≤ k ≤ m`,
`α_1 + ... + α_k ≥ 0`, strictly when `n > 2m`. -/
theorem conjecture (n m k : ℕ) (hm : 1 ≤ m) (hn : 2 * m ≤ n) (hk1 : 1 ≤ k) (hk : k ≤ m) :
    0 ≤ ∑ i ∈ Finset.Icc 1 k, A n m i := by
  rcases hn.lt_or_eq with hlt | heq
  · exact (partial_sum_pos n m k hm hlt hk1 (by omega)).le
  · subst heq
    rw [sum_eq_zero fun i hi => A_symm_zero m i (by simp only [mem_Icc] at hi; omega)]

end SimmonsPartial
