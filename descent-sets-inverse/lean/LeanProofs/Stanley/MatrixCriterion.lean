/- Exact joint descents from positive crossings in a run-margin matrix.
This is an exact reformulation, not a proof of dominance sufficiency. -/
import LeanProofs.Stanley.Contingency
import LeanProofs.Stanley.JointMultiplicity

namespace Stanley.Alt.Contingency
open Finset Equiv

def RowCross {n : ℕ} (M : Fin (n+1) → Fin (n+1) → ℕ)
    (A : Finset ℕ) (i : ℕ) (hi : i+1<n) : Prop :=
  ∃ j k, k<j ∧ 0<M (blk n A ⟨i,by omega⟩) j ∧ 0<M (blk n A ⟨i+1,hi⟩) k

def Crosses {n : ℕ} (M : Fin (n+1) → Fin (n+1) → ℕ) (A : Finset ℕ) : Prop :=
  ∀ i ∈ A, ∃ hi : i+1<n, RowCross M A i hi

theorem block_succ_gt {n : ℕ} {A : Finset ℕ} {i : ℕ} (hA : i∈A) (hi : i+1<n) :
    blk n A ⟨i,by omega⟩ < blk n A ⟨i+1,hi⟩ := by
  have hle := block_monotone A (Nat.le_succ i)
  simp only [Nat.succ_eq_add_one] at hle
  have hne : block A (i+1)≠block A i := by
    intro h; exact (block_succ_eq_iff A i).mp h hA
  change block A i < block A (i+1)
  omega

theorem row_before_boundary {n : ℕ} {A : Finset ℕ} {i : ℕ} (hA : i∈A)
    (hi : i+1<n) {p : Fin n} (hp : blk n A p=blk n A ⟨i,by omega⟩) : (p : ℕ) ≤ i := by
  by_contra hnot
  have hg := block_succ_gt hA hi
  have hm := blk_mono A (p := ⟨i+1,hi⟩) (q := p) (by change i+1 ≤ p.val; omega)
  rw [hp] at hm
  exact not_le_of_gt hg hm

theorem row_after_boundary {n : ℕ} {A : Finset ℕ} {i : ℕ} (hA : i∈A)
    (hi : i+1<n) {p : Fin n} (hp : blk n A p=blk n A ⟨i+1,hi⟩) : i+1≤(p:ℕ) := by
  by_contra hnot
  have hg := block_succ_gt hA hi
  have hm := blk_mono A (p := p) (q := ⟨i,by omega⟩) (by change p.val ≤ i; omega)
  rw [hp] at hm
  exact not_le_of_gt hg hm

theorem rowCross_iff_descent {n : ℕ} (A B : Finset ℕ) (w : Perm (Fin n))
    (hwA : descP w ⊆ A) (hwB : descP w⁻¹ ⊆ B) {i : ℕ} (hi : i+1<n)
    (hA : i∈A) : RowCross (ofPerm A B w) A i hi ↔ i∈descP w := by
  let l : Fin n := ⟨i,by omega⟩
  let r : Fin n := ⟨i+1,hi⟩
  have hmA := (descP_subset_iff_blocks w A).mp hwA
  have hmB := (descP_subset_iff_blocks w⁻¹ B).mp hwB
  constructor
  · rintro ⟨j,k,hkj,hj,hk⟩
    unfold ofPerm cell at hj hk
    obtain ⟨p,hp⟩ := card_pos.mp hj
    obtain ⟨q,hq⟩ := card_pos.mp hk
    obtain ⟨_,hpA,hpB⟩ := mem_filter.mp hp
    obtain ⟨_,hqA,hqB⟩ := mem_filter.mp hq
    change blk n B (w p)=j at hpB
    change blk n B (w q)=k at hqB
    have hpi := row_before_boundary hA hi hpA
    have hiq := row_after_boundary hA hi hqA
    have hpl : w p≤w l := by
      rcases lt_or_eq_of_le hpi with h | h
      · exact (hmA p l (congrArg Fin.val hpA) (by rw [Fin.lt_def]; exact h)).le
      · have he : p=l := Fin.ext h
        rw [he]
    have hrq : w r≤w q := by
      rcases lt_or_eq_of_le hiq with h | h
      · exact (hmA r q (congrArg Fin.val hqA).symm (by rw [Fin.lt_def]; exact h)).le
      · have he : r=q := Fin.ext h
        rw [he]
    have hqp : w q<w p := by
      by_contra hn
      have hh := blk_mono B (not_lt.mp hn)
      change blk n B (w p)≤blk n B (w q) at hh
      rw [hpB,hqB] at hh
      exact not_le_of_gt hkj hh
    apply mem_descP.mpr
    exact ⟨hi,lt_of_le_of_lt hrq (lt_of_lt_of_le hqp hpl)⟩
  · intro hd
    obtain ⟨_,hd⟩ := mem_descP.mp hd
    have hwr : w r<w l := hd
    have hbl : blk n B (w r)<blk n B (w l) := by
      have hle := blk_mono B hwr.le
      have hne : blk n B (w r)≠blk n B (w l) := by
        intro he
        have hh := hmB (w r) (w l) (congrArg Fin.val he) hwr
        have hr : w⁻¹ (w r)=r := by simp
        have hl : w⁻¹ (w l)=l := by simp
        rw [hr,hl,Fin.lt_def] at hh
        dsimp [r,l] at hh
        omega
      exact lt_of_le_of_ne hle hne
    refine ⟨blk n B (w l),blk n B (w r),hbl,?_,?_⟩
    · unfold ofPerm cell
      apply card_pos.mpr
      exact ⟨l,by simp [ofPerm,cell,l]⟩
    · unfold ofPerm cell
      apply card_pos.mpr
      exact ⟨r,by simp [ofPerm,cell,r]⟩

/-- Exact occurrence iff an integer run-margin matrix has every prescribed crossing. -/
theorem beta_pos_iff_matrix {n : ℕ} (A B : Finset ℕ)
    (hA : A ⊆ range (n-1)) (hB : B ⊆ range (n-1)) :
    0<Stanley.beta n A B ↔ ∃ M : Fin (n+1) → Fin (n+1) → ℕ,
      (∀ i,∑ j,M i j=fib (blk n A) i) ∧
      (∀ j,∑ i,M i j=fib (blk n B) j) ∧ Crosses M A ∧ Crosses (fun j i=>M i j) B := by
  rw [Stanley.beta_pos_iff_mem_pairs]
  constructor
  · intro hp
    obtain ⟨w,_,he⟩ := mem_image.mp hp
    have hwA : descP w=A := congrArg Prod.fst he
    have hwB : descP w⁻¹=B := congrArg Prod.snd he
    refine ⟨ofPerm A B w,ofPerm_rows A B w,ofPerm_cols A B w,?_,?_⟩
    · intro i hi
      have hin := mem_range.mp (hA hi)
      refine ⟨by omega,?_⟩
      exact (rowCross_iff_descent A B w (by rw [hwA]) (by rw [hwB])
        (by omega) hi).mpr (hwA.symm ▸ hi)
    · intro j hj
      have hjn := mem_range.mp (hB hj)
      refine ⟨by omega,?_⟩
      have ht : (fun j i=>ofPerm A B w i j)=ofPerm B A w⁻¹ := by
        funext j i; exact (ofPerm_inv A B w i j).symm
      rw [ht]
      exact (rowCross_iff_descent B A w⁻¹ (by simpa using hwB.le)
        (by simpa using hwA.le) (by omega) hj).mpr (hwB.symm ▸ hj)
  · rintro ⟨M,hrow,hcol,hcross,hcross'⟩
    obtain ⟨w,hwA,hwB,he⟩ := exists_of_margins A B M hrow hcol
    have hwa : descP w=A := by
      apply Subset.antisymm hwA
      intro i hi
      obtain ⟨hin,hh⟩ := hcross i hi
      rw [←he] at hh
      exact (rowCross_iff_descent A B w hwA hwB hin hi).mp hh
    have hwb : descP w⁻¹=B := by
      apply Subset.antisymm hwB
      intro j hj
      obtain ⟨hjn,hh⟩ := hcross' j hj
      have ht : (fun j i=>M i j)=ofPerm B A w⁻¹ := by
        funext j i; rw [ofPerm_inv,he]
      rw [ht] at hh
      exact (rowCross_iff_descent B A w⁻¹ hwB (by simpa using hwA) hjn hj).mp hh
    exact mem_image.mpr ⟨w,mem_univ _,by change (descP w,descP w⁻¹)=(A,B); rw [hwa,hwb]⟩

/-- Exact joint multiplicity counts the integer matrices with all prescribed crossings. -/
theorem beta_eq_card_matrices {n : ℕ} (A B : Finset ℕ)
    (hA : A ⊆ range (n-1)) (hB : B ⊆ range (n-1)) :
    Stanley.beta n A B = Nat.card {M : Fin (n+1) → Fin (n+1) → ℕ //
      (∀ i, ∑ j, M i j = fib (blk n A) i) ∧
      (∀ j, ∑ i, M i j = fib (blk n B) j) ∧ Crosses M A ∧
        Crosses (fun j i => M i j) B} := by
  classical
  have hc : Stanley.beta n A B =
      Nat.card {w : Perm (Fin n) // descP w=A ∧ descP w⁻¹=B} := by
    rw [Nat.card_eq_fintype_card,Fintype.card_subtype]; rfl
  rw [hc]
  let f : {w : Perm (Fin n) // descP w=A ∧ descP w⁻¹=B} →
      {M : Fin (n+1) → Fin (n+1) → ℕ //
      (∀ i, ∑ j, M i j = fib (blk n A) i) ∧
      (∀ j, ∑ i, M i j = fib (blk n B) j) ∧ Crosses M A ∧
        Crosses (fun j i => M i j) B} := fun w =>
      ⟨ofPerm A B w.1,ofPerm_rows A B w.1,ofPerm_cols A B w.1,by
        intro i hi
        have hin := mem_range.mp (hA hi)
        refine ⟨by omega,?_⟩
        exact (rowCross_iff_descent A B w.1 w.2.1.le w.2.2.le
          (by omega) hi).mpr (w.2.1.symm ▸ hi),by
        intro j hj
        have hjn := mem_range.mp (hB hj)
        refine ⟨by omega,?_⟩
        have ht : (fun j i=>ofPerm A B w.1 i j)=ofPerm B A w.1⁻¹ := by
          funext j i; exact (ofPerm_inv A B w.1 i j).symm
        rw [ht]
        exact (rowCross_iff_descent B A w.1⁻¹ w.2.2.le
          (by simpa using w.2.1.le) (by omega) hj).mpr (w.2.2.symm ▸ hj)⟩
  apply Nat.card_eq_of_bijective f
  constructor
  · intro w v he
    apply Subtype.ext
    exact ofPerm_injective A B w.1 v.1 w.2.1.le w.2.2.le v.2.1.le v.2.2.le
      (congrArg Subtype.val he)
  · intro M
    obtain ⟨w,hwA,hwB,he⟩ := exists_of_margins A B M.1 M.2.1 M.2.2.1
    have hwa : descP w=A := by
      apply Subset.antisymm hwA
      intro i hi
      obtain ⟨hin,hh⟩ := M.2.2.2.1 i hi
      rw [←he] at hh
      exact (rowCross_iff_descent A B w hwA hwB hin hi).mp hh
    have hwb : descP w⁻¹=B := by
      apply Subset.antisymm hwB
      intro j hj
      obtain ⟨hjn,hh⟩ := M.2.2.2.2 j hj
      have ht : (fun j i=>M.1 i j)=ofPerm B A w⁻¹ := by
        funext j i; rw [ofPerm_inv,he]
      rw [ht] at hh
      exact (rowCross_iff_descent B A w⁻¹ hwB (by simpa using hwA) hjn hj).mp hh
    exact ⟨⟨w,hwa,hwb⟩,Subtype.ext he⟩

end Stanley.Alt.Contingency
