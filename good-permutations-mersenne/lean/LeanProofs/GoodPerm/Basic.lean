import Mathlib

/-!
# Good permutations (MO 514690): definitions

Positions are `1..n`; a permutation is a function `f : ℕ → ℤ` that maps `1..n` injectively into
`1..n`. `S f t L` is the sum of the block of length `L` starting at position `t`. The permutation is
*good* if no proper block of length at least 2 has an integer average.
* `S_add`, `S_shift`, `S_one`: splitting and sliding blocks;
* `perm_sum`: a permutation of `1..n` has the same sum as `1, 2, ..., n`;
* `two_mul_sum_id`: `2 (1 + ... + n) = n (n + 1)`.
-/

open Finset

namespace GoodPerm

/-- The sum of the block of length `L` starting at position `t`. -/
def S (f : ℕ → ℤ) (t L : ℕ) : ℤ := ∑ i ∈ range L, f (t + i)

/-- `f` maps the positions `1..n` injectively into `1..n`. -/
def IsPerm (n : ℕ) (f : ℕ → ℤ) : Prop :=
  (∀ t, 1 ≤ t → t ≤ n → 1 ≤ f t ∧ f t ≤ n) ∧
    ∀ s t, 1 ≤ s → s ≤ n → 1 ≤ t → t ≤ n → f s = f t → s = t

/-- Good: every proper block of length at least 2 has a non-integer average. -/
def Good (n : ℕ) (f : ℕ → ℤ) : Prop :=
  ∀ t L, 1 ≤ t → 2 ≤ L → L < n → t + L ≤ n + 1 → ¬ (L : ℤ) ∣ S f t L

lemma S_add (f : ℕ → ℤ) (t L M : ℕ) : S f t (L + M) = S f t L + S f (t + L) M := by
  simp only [S, sum_range_add]
  congr 1
  exact sum_congr rfl fun i _ => by rw [add_assoc]

lemma S_shift (f : ℕ → ℤ) (t L : ℕ) : S f t L + f (t + L) = f t + S f (t + 1) L := by
  simp only [S]
  rw [← sum_range_succ (fun i => f (t + i)), sum_range_succ', add_zero, add_comm]
  congr 1
  exact sum_congr rfl fun i _ => by congr 1; omega

lemma S_one (f : ℕ → ℤ) (L : ℕ) : S f 1 (L + 1) = f 1 + S f 2 L := by
  rw [show L + 1 = 1 + L by ring, S_add]
  simp [S]

lemma two_mul_sum_id (n : ℕ) : 2 * ∑ i ∈ range n, ((1 + i : ℕ) : ℤ) = n * (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih => rw [sum_range_succ, mul_add, ih]; push_cast; ring

/-- A permutation of `1..n` has the same sum as `1, ..., n`. -/
lemma perm_sum {n : ℕ} {f : ℕ → ℤ} (hf : IsPerm n f) :
    ∑ i ∈ range n, f (1 + i) = ∑ i ∈ range n, ((1 + i : ℕ) : ℤ) := by
  have hI : (Icc (1 : ℤ) n).card = n := by simp
  have hA : (range n).image (fun i => f (1 + i)) = Icc (1 : ℤ) n := by
    refine eq_of_subset_of_card_le (fun v hv => ?_) ?_
    · obtain ⟨i, hi, rfl⟩ := mem_image.1 hv
      have := hf.1 (1 + i) (by omega) (by simp at hi; omega)
      exact mem_Icc.2 this
    · rw [hI, card_image_of_injOn (fun i hi j hj h => by
        have := hf.2 (1 + i) (1 + j) (by omega) (by simp at hi; omega) (by omega)
          (by simp at hj; omega) h
        omega), card_range]
  have hB : (range n).image (fun i => ((1 + i : ℕ) : ℤ)) = Icc (1 : ℤ) n := by
    refine eq_of_subset_of_card_le (fun v hv => ?_) ?_
    · obtain ⟨i, hi, rfl⟩ := mem_image.1 hv
      simp at hi ⊢; omega
    · rw [hI, card_image_of_injOn (fun i _ j _ h => by simp at h; omega), card_range]
  have e1 := sum_image (s := range n) (f := id) (g := fun i => f (1 + i)) (fun i hi j hj h => by
    have := hf.2 (1 + i) (1 + j) (by omega) (by simp at hi; omega) (by omega)
      (by simp at hj; omega) h
    omega)
  have e2 := sum_image (s := range n) (f := id) (g := fun i => ((1 + i : ℕ) : ℤ))
    (fun i _ j _ h => by simp at h; omega)
  simp only [id] at e1 e2
  rw [← e1, ← e2, hA, hB]

end GoodPerm
