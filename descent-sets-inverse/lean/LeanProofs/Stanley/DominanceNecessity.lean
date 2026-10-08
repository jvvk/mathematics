/- The two Gale–Ryser inequalities forced by a joint descent pair.
Run lengths are represented by their actual block fibres. -/
import LeanProofs.Stanley.MatrixCriterion
import Mathlib.Data.Fin.Rev

namespace Stanley.Alt
open Finset Equiv
open Contingency

def complementCuts (n : ℕ) (A : Finset ℕ) := range (n-1) \ A

theorem descP_reverse_values {n : ℕ} (w : Perm (Fin n)) :
    descP (Fin.revPerm * w) = complementCuts n (descP w) := by
  ext i
  simp only [complementCuts,mem_sdiff,mem_range,mem_descP]
  constructor
  · rintro ⟨hi,hd⟩
    have hh : w ⟨i,by omega⟩ < w ⟨i+1,hi⟩ := by
      simpa only [Perm.mul_apply,Fin.revPerm_apply,Fin.rev_lt_rev] using hd
    refine ⟨by omega,?_⟩
    rintro ⟨hi',hh'⟩
    exact (not_lt_of_gt hh) hh'
  · rintro ⟨hi,hn⟩
    have hin : i+1<n := by omega
    refine ⟨hin,?_⟩
    have hne : w ⟨i,by omega⟩ ≠ w ⟨i+1,hin⟩ := by
      intro h
      have he := w.injective h
      have hv := congrArg Fin.val he
      dsimp at hv
      omega
    have hh : w ⟨i,by omega⟩ < w ⟨i+1,hin⟩ := by
      apply lt_of_le_of_ne
      · exact not_lt.mp (fun h => hn ⟨hin,h⟩)
      · exact hne
    simpa only [Perm.mul_apply,Fin.revPerm_apply,Fin.rev_lt_rev] using hh

/-- Inside a decreasing run, values strictly decrease with the index. -/
theorem strictAnti_blocks {n : ℕ} (w : Perm (Fin n)) {p q : Fin n}
    (hblock : blk n (complementCuts n (descP w)) p =
      blk n (complementCuts n (descP w)) q) (hpq : p<q) : w q<w p := by
  have hh := (descP_subset_iff_blocks (Fin.revPerm * w)
    (complementCuts n (descP w))).mp (by rw [descP_reverse_values]) p q
      (congrArg Fin.val hblock) hpq
  simpa only [Perm.mul_apply,Fin.revPerm_apply,Fin.rev_lt_rev] using hh

/-- An increasing position run and a decreasing value run share at most one entry. -/
theorem increasing_decreasing_cell_le_one {n : ℕ} (w : Perm (Fin n)) (i j : Fin (n+1)) :
    ofPerm (descP w) (complementCuts n (descP w⁻¹)) w i j ≤ 1 := by
  unfold ofPerm cell
  apply card_le_one.mpr
  intro p hp q hq
  obtain ⟨_,hpA,hpB⟩ := mem_filter.mp hp
  obtain ⟨_,hqA,hqB⟩ := mem_filter.mp hq
  have hpos := congrArg Fin.val (hpA.trans hqA.symm)
  have hval := hpB.trans hqB.symm
  change blk n (complementCuts n (descP w⁻¹)) (w p) =
    blk n (complementCuts n (descP w⁻¹)) (w q) at hval
  rcases lt_trichotomy p q with h | h | h
  · have hinc := (descP_subset_iff_blocks w (descP w)).mp (Subset.rfl) p q hpos h
    have hdec := strictAnti_blocks w⁻¹ hval hinc
    have hbad : q<p := by simpa using hdec
    exact False.elim ((not_lt_of_gt h) hbad)
  · exact h
  · have hinc := (descP_subset_iff_blocks w (descP w)).mp (Subset.rfl) q p hpos.symm h
    have hdec := strictAnti_blocks w⁻¹ hval.symm hinc
    have hbad : p<q := by simpa using hdec
    exact False.elim ((not_lt_of_gt h) hbad)

/-- Subset form of the Gale–Ryser dominance inequalities. -/
def RunDominance (n : ℕ) (A B : Finset ℕ) : Prop :=
  ∀ R : Finset (Fin (n+1)), ∑ i ∈ R, fib (blk n A) i ≤
    ∑ j : Fin (n+1), min R.card (fib (blk n B) j)

theorem binary_matrix_bound {n : ℕ} (A B : Finset ℕ) (w : Perm (Fin n))
    (hbinary : ∀ i j, ofPerm A B w i j ≤ 1) : RunDominance n A B := by
  intro R
  calc
    ∑ i ∈ R, fib (blk n A) i = ∑ i ∈ R, ∑ j, ofPerm A B w i j := by
      simp_rw [ofPerm_rows]
    _ = ∑ j, ∑ i ∈ R, ofPerm A B w i j := sum_comm
    _ ≤ ∑ j, min R.card (fib (blk n B) j) := by
      apply sum_le_sum
      intro j _
      apply le_min
      · calc
          ∑ i ∈ R, ofPerm A B w i j ≤ ∑ i ∈ R, 1 :=
            sum_le_sum (fun i _ => hbinary i j)
          _ = R.card := by simp
      · calc
          ∑ i ∈ R, ofPerm A B w i j ≤ ∑ i, ofPerm A B w i j :=
            sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun _ _ _ => Nat.zero_le _)
          _ = fib (blk n B) j := ofPerm_cols A B w j

/-- Both cross-dominance conditions are necessary for positive joint multiplicity. -/
theorem beta_pos_implies_cross_dominance {n : ℕ} (A B : Finset ℕ)
    (h : 0<Stanley.beta n A B) :
    RunDominance n A (complementCuts n B) ∧
      RunDominance n B (complementCuts n A) := by
  obtain ⟨w,_,he⟩ := mem_image.mp ((Stanley.beta_pos_iff_mem_pairs n A B).mp h)
  have hA : descP w=A := congrArg Prod.fst he
  have hB : descP w⁻¹=B := congrArg Prod.snd he
  have h1 := binary_matrix_bound (descP w) (complementCuts n (descP w⁻¹)) w
    (increasing_decreasing_cell_le_one w)
  have h2 := binary_matrix_bound (descP w⁻¹) (complementCuts n (descP w)) w⁻¹
    (by simpa using increasing_decreasing_cell_le_one w⁻¹)
  simpa [hA,hB] using And.intro h1 h2

end Stanley.Alt
