/-
  Exact inclusion-exclusion for the joint descent count. This is an unconditional
  starting point for the Stanley generating-function proof completed in StanleyProof.lean.
-/
import LeanProofs.Stanley.AltBasic

namespace Stanley.Alt

open Finset

theorem subset_sdiff_iff {A D S : Finset ℕ} (hDA : D ⊆ A) :
    D ⊆ A \ S ↔ ∀ i ∈ S, i ∉ D := by
  constructor
  · intro h i hi hD
    exact (mem_sdiff.mp (h hD)).2 hi
  · intro h i hi
    exact mem_sdiff.mpr ⟨hDA hi, fun hS => h i hS hi⟩

/-- Möbius inversion on the Boolean lattice, written with deleted subsets. -/
theorem descent_indicator (A D : Finset ℕ) :
    (∑ S ∈ A.powerset, (-1 : ℝ) ^ S.card * if D ⊆ A \ S then 1 else 0) =
      if D = A then 1 else 0 := by
  classical
  by_cases hDA : D ⊆ A
  · have hp := Finset.prod_one_add (f := fun i : ℕ => if i ∉ D then (-1 : ℝ) else 0) A
    have ht : ∀ S : Finset ℕ,
        (∏ i ∈ S, if i ∉ D then (-1 : ℝ) else 0) =
          (-1 : ℝ) ^ S.card * if D ⊆ A \ S then 1 else 0 := by
      intro S
      rw [Finset.prod_ite_zero, Finset.prod_const]
      simp only [subset_sdiff_iff hDA]
      split_ifs <;> simp
    have hl : (∏ i ∈ A, (1 + if i ∉ D then (-1 : ℝ) else 0)) =
        if A ⊆ D then 1 else 0 := by
      trans ∏ i ∈ A, (if i ∈ D then (1 : ℝ) else 0)
      · apply prod_congr rfl; intro i _; by_cases h : i ∈ D <;> simp [h]
      · rw [Finset.prod_boole]; rfl
    rw [hl] at hp
    simp_rw [ht] at hp
    rw [← hp]
    by_cases hAD : A ⊆ D
    · simp [Finset.Subset.antisymm hDA hAD]
    · have hn : D ≠ A := fun h => hAD (h ▸ Finset.Subset.refl _)
      simp [hAD, hn]
  · have hn : D ≠ A := fun h => hDA (h ▸ Finset.Subset.refl _)
    rw [ite_eq_right hn]
    apply sum_eq_zero
    intro S _
    rw [ite_eq_right (fun h => hDA (h.trans sdiff_subset)), mul_zero]

theorem cast_card_filter {Ω : Type*} [Fintype Ω] (P : Ω → Prop) [DecidablePred P] :
    (((univ : Finset Ω).filter P).card : ℝ) = ∑ w : Ω, if P w then (1 : ℝ) else 0 := by
  rw [Finset.card_filter]
  push_cast
  rfl

/-- Count with both descent sets contained in prescribed allowed sets. -/
def jointSubsetCount (n : ℕ) (A B : Finset ℕ) : ℕ :=
  ((univ : Finset (Equiv.Perm (Fin n))).filter
    (fun w => descP w ⊆ A ∧ descP w⁻¹ ⊆ B)).card

/-- Exact joint descent counts are signed sums of joint subset counts. -/
theorem joint_descent_count (n : ℕ) (A B : Finset ℕ) :
    (((univ : Finset (Equiv.Perm (Fin n))).filter
      (fun w => descP w = A ∧ descP w⁻¹ = B)).card : ℝ) =
      ∑ S ∈ A.powerset, ∑ T ∈ B.powerset,
        (-1 : ℝ) ^ (S.card + T.card) * (jointSubsetCount n (A \ S) (B \ T) : ℝ) := by
  rw [cast_card_filter]
  calc
    (∑ w : Equiv.Perm (Fin n), if descP w = A ∧ descP w⁻¹ = B then (1 : ℝ) else 0) =
        ∑ w : Equiv.Perm (Fin n),
          (∑ S ∈ A.powerset, (-1 : ℝ) ^ S.card * if descP w ⊆ A \ S then 1 else 0) *
          (∑ T ∈ B.powerset, (-1 : ℝ) ^ T.card * if descP w⁻¹ ⊆ B \ T then 1 else 0) := by
      apply sum_congr rfl
      intro w _
      rw [descent_indicator, descent_indicator]
      by_cases hA : descP w = A <;> by_cases hB : descP w⁻¹ = B <;> simp [hA, hB]
    _ = ∑ w : Equiv.Perm (Fin n), ∑ S ∈ A.powerset, ∑ T ∈ B.powerset,
        (-1 : ℝ) ^ (S.card + T.card) *
          if descP w ⊆ A \ S ∧ descP w⁻¹ ⊆ B \ T then 1 else 0 := by
      apply sum_congr rfl; intro w _
      rw [sum_mul]
      simp_rw [mul_sum]
      apply sum_congr rfl; intro S _
      apply sum_congr rfl; intro T _
      rw [pow_add]
      by_cases hA : descP w ⊆ A \ S <;> by_cases hB : descP w⁻¹ ⊆ B \ T <;> simp [hA, hB]
    _ = ∑ S ∈ A.powerset, ∑ T ∈ B.powerset, ∑ w : Equiv.Perm (Fin n),
        (-1 : ℝ) ^ (S.card + T.card) *
          if descP w ⊆ A \ S ∧ descP w⁻¹ ⊆ B \ T then 1 else 0 := by
      rw [sum_comm]
      apply sum_congr rfl; intro S _; rw [sum_comm]
    _ = _ := by
      apply sum_congr rfl; intro S _
      apply sum_congr rfl; intro T _
      rw [jointSubsetCount, cast_card_filter, mul_sum]

theorem g_inclusion_exclusion (n : ℕ) :
    (g n : ℝ) = ∑ S ∈ (altS n).powerset, ∑ T ∈ (altS n).powerset,
      (-1 : ℝ) ^ (S.card + T.card) *
        (jointSubsetCount n (altS n \ S) (altS n \ T) : ℝ) :=
  joint_descent_count n (altS n) (altS n)

end Stanley.Alt
