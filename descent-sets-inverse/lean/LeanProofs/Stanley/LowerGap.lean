/- Remark 3.4: the density gap is at most exponential with rate log 2.
No pair (∅, T) with T nonempty occurs, since no descents forces the identity. -/
import LeanProofs.Stanley.TwoBlocks

namespace Stanley
open Finset

/-- A permutation with no descents has inverse with no descents. -/
theorem not_mem_pairs_empty {n : ℕ} {T : Finset ℕ} (hT : T.Nonempty) : (∅, T) ∉ pairs n := by
  intro h
  obtain ⟨w, _, he⟩ := mem_image.mp h
  have hw : w = 1 := (TwoBlocks.descP_empty_iff w).mp (congrArg Prod.fst he)
  have hi : descP w⁻¹ = T := congrArg Prod.snd he
  rw [hw, inv_one, ((TwoBlocks.descP_empty_iff (1 : Equiv.Perm (Fin n))).mpr rfl)] at hi
  exact hT.ne_empty hi.symm

/-- `f n + (2^(n-1) - 1) ≤ 4^(n-1)`: the pairs `(∅, T)`, `T ≠ ∅`, never occur. -/
theorem f_add_le (n : ℕ) : f n + (2 ^ (n - 1) - 1) ≤ 4 ^ (n - 1) := by
  set P := (range (n - 1)).powerset
  have hsub : pairs n ⊆ P ×ˢ P := by
    intro st hst
    obtain ⟨σ, _, rfl⟩ := mem_image.mp hst
    simp only [P, mem_product, mem_powerset]
    exact ⟨filter_subset _ _, filter_subset _ _⟩
  have hbad : ({∅} : Finset (Finset ℕ)) ×ˢ P.erase ∅ ⊆ P ×ˢ P := by
    intro st hst
    simp only [mem_product, mem_singleton, mem_erase] at hst
    simp only [P, mem_product, mem_powerset, hst.1, empty_subset, true_and]
    exact mem_powerset.mp hst.2.2
  have hdisj : Disjoint (pairs n) (({∅} : Finset (Finset ℕ)) ×ˢ P.erase ∅) := by
    apply disjoint_right.mpr
    rintro ⟨S, T⟩ hst
    simp only [mem_product, mem_singleton, mem_erase] at hst
    obtain ⟨rfl, hT, _⟩ := hst
    exact not_mem_pairs_empty (nonempty_iff_ne_empty.mpr hT)
  have hcard := card_le_card (union_subset hsub hbad)
  rw [card_union_of_disjoint hdisj, card_product, card_product, card_singleton,
    card_erase_of_mem (mem_powerset.mpr (empty_subset _)), card_powerset, card_range] at hcard
  calc f n + (2 ^ (n - 1) - 1) = (pairs n).card + 1 * (2 ^ (n - 1) - 1) := by rw [one_mul]; rfl
    _ ≤ 2 ^ (n - 1) * 2 ^ (n - 1) := hcard
    _ = 4 ^ (n - 1) := by rw [← mul_pow]; norm_num

/-- **Remark 3.4.** `1 - f(n)/4^(n-1) ≥ (2^(n-1) - 1)/4^(n-1)` for every `n`. -/
theorem density_gap_lower (n : ℕ) :
    ((2 : ℝ) ^ (n - 1) - 1) / 4 ^ (n - 1) ≤ 1 - (f n : ℝ) / 4 ^ (n - 1) := by
  have h := f_add_le n
  have h1 : 1 ≤ 2 ^ (n - 1) := Nat.one_le_two_pow
  have hc : ((f n : ℕ) : ℝ) + ((2 : ℝ) ^ (n - 1) - 1) ≤ (4 : ℝ) ^ (n - 1) := by
    have := (Nat.cast_le (α := ℝ)).mpr h
    push_cast [Nat.cast_sub h1] at this
    linarith
  have hpos : (0 : ℝ) < 4 ^ (n - 1) := by positivity
  rw [div_le_iff₀ hpos, sub_mul, div_mul_cancel₀ _ hpos.ne', one_mul]
  linarith

end Stanley
