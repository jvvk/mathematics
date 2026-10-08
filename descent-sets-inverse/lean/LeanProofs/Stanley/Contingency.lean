/- Nonnegative contingency matrices for joint subset descent conditions.
Margins are the actual run-block fibre sizes; matrix cells are actual
intersection cardinalities. -/
import LeanProofs.Stanley.DoubleCoset

namespace Stanley.Alt
open Finset Equiv
namespace Contingency

def cell {n : ℕ} {I J : Type*} [DecidableEq I] [DecidableEq J]
    (f : Fin n → I) (g : Fin n → J) (i : I) (j : J) : ℕ :=
  (univ.filter (fun p => f p=i ∧ g p=j)).card

theorem cell_comp {n : ℕ} {I J : Type*} [DecidableEq I] [DecidableEq J]
    (f : Fin n → I) (g : Fin n → J) (σ : Perm (Fin n)) (i : I) (j : J) :
    cell (f ∘ σ) (g ∘ σ) i j = cell f g i j := by
  apply card_bij (fun p _ => σ p)
  · intro p hp; simpa only [mem_filter,mem_univ,true_and,Function.comp_apply] using hp
  · intro p _ q _ h; exact σ.injective h
  · intro p hp
    refine ⟨σ⁻¹ p,?_,by simp⟩
    simpa [Function.comp_def] using hp

theorem row_sum {n : ℕ} {I J : Type*} [DecidableEq I] [DecidableEq J] [Fintype J]
    (f : Fin n → I) (g : Fin n → J) (i : I) : ∑ j, cell f g i j = fib f i := by
  unfold cell fib
  have h := Finset.card_eq_sum_card_fiberwise (s := univ.filter (fun p => f p=i))
    (t := univ) (f := g) (by intro p _; exact mem_univ _)
  rw [h]
  apply sum_congr rfl
  intro j _
  congr 1
  ext p
  simp

theorem col_sum {n : ℕ} {I J : Type*} [DecidableEq I] [DecidableEq J] [Fintype I]
    (f : Fin n → I) (g : Fin n → J) (j : J) : ∑ i, cell f g i j = fib g j := by
  have h : ∀ i, cell f g i j=cell g f j i := by intro i; unfold cell; congr 1; ext p; simp [and_comm]
  simp_rw [h]
  exact row_sum g f j

def ofPerm {n : ℕ} (A B : Finset ℕ) (w : Perm (Fin n)) :
    Fin (n+1) → Fin (n+1) → ℕ := cell (blk n A) (blk n B ∘ w)

theorem ofPerm_rows {n : ℕ} (A B : Finset ℕ) (w : Perm (Fin n)) (i : Fin (n+1)) :
    ∑ j, ofPerm A B w i j = fib (blk n A) i := row_sum _ _ _

theorem ofPerm_cols {n : ℕ} (A B : Finset ℕ) (w : Perm (Fin n)) (j : Fin (n+1)) :
    ∑ i, ofPerm A B w i j = fib (blk n B) j := by
  rw [ofPerm,col_sum,fib_comp]

theorem ofPerm_inv {n : ℕ} (A B : Finset ℕ) (w : Perm (Fin n)) (i j : Fin (n+1)) :
    ofPerm B A w⁻¹ j i = ofPerm A B w i j := by
  have h := cell_comp (blk n B) (blk n A ∘ ⇑(w⁻¹)) w j i
  have he : (blk n A ∘ ⇑(w⁻¹)) ∘ w=blk n A := by funext p; simp
  rw [he] at h
  rw [ofPerm,ofPerm,←h]
  unfold cell
  congr 1
  ext p
  simp [and_comm]

theorem cell_of_orbit_eq {n : ℕ} {A B : Finset ℕ}
    {f1 f2 : Flag n A} {g1 g2 : Flag n B}
    (h : (Quotient.mk (MulAction.orbitRel (Perm (Fin n)) _) (f1,g1)) =
      Quotient.mk (MulAction.orbitRel (Perm (Fin n)) _) (f2,g2)) :
    cell f1.1 g1.1 = cell f2.1 g2.1 := by
  rw [Quotient.eq,MulAction.orbitRel_apply,MulAction.mem_orbit_iff] at h
  obtain ⟨σ,hσ⟩ := h
  have hf : f1.1=f2.1 ∘ ⇑(σ⁻¹) := by
    exact (congrArg (fun x : Flag n A × Flag n B => x.1.1) hσ).symm
  have hg : g1.1=g2.1 ∘ ⇑(σ⁻¹) := by
    exact (congrArg (fun x : Flag n A × Flag n B => x.2.1) hσ).symm
  funext i j
  rw [hf,hg,cell_comp]

/-- Concrete flags have a representative with both subset descent conditions. -/
theorem exists_monotone_rep {n : ℕ} (A B : Finset ℕ) (f1 : Flag n A) (f2 : Flag n B) :
    ∃ w : Perm (Fin n), descP w ⊆ A ∧ descP w⁻¹ ⊆ B ∧
      orbOf A B w = Quotient.mk (MulAction.orbitRel _ _) (f1,f2) := by
  classical
  obtain ⟨σ1,hσ1⟩ := exists_perm_of_flag f1
  have hx1 : σ1 • f1=canon n A := Subtype.ext (by
    funext p; rw [smul_val]; simp [hσ1,canon])
  obtain ⟨π,hπ⟩ := exists_perm_of_flag (σ1 • f2)
  have hgπ : σ1 • f2=gflag n B π := Subtype.ext hπ
  have hq : orbOf A B π=Quotient.mk (MulAction.orbitRel _ _) (f1,f2) := by
    unfold orbOf; rw [←hx1,←hgπ,←Prod.smul_mk,mk_smul]
  let D := univ.filter (fun w : Perm (Fin n) => orbOf A B w=orbOf A B π)
  obtain ⟨w,hwD,hmin⟩ := D.exists_min_image (fun w => (invs w).card) ⟨π,by simp [D]⟩
  have hw : orbOf A B w=orbOf A B π := (mem_filter.mp hwD).2
  refine ⟨w,?_,?_,hw.trans hq⟩
  · intro i hi
    by_contra hA
    obtain ⟨hi1,hd⟩ := mem_descP.mp hi
    let a : Fin n := ⟨i,by omega⟩
    let a' : Fin n := ⟨i+1,hi1⟩
    have haa : (a':ℕ)=a+1 := rfl
    have hstay : orbOf A B (w * swap a a')=orbOf A B w := by
      have e : swap a a' • (canon n A,gflag n B w)=
          (canon n A,gflag n B (w * swap a a')) := by
        rw [Prod.smul_mk]
        congr 1
        exact Subtype.ext (by funext p; rw [smul_val,swap_inv]; exact blk_swap A haa hA p)
      unfold orbOf; rw [←e,mk_smul]
    have hm : w * swap a a' ∈ D := by simp [D,hstay,hw]
    exact absurd (hmin _ hm) (not_le.mpr (card_invs_swap_right w haa hd))
  · intro i hi
    by_contra hB
    obtain ⟨hi1,hd⟩ := mem_descP.mp hi
    let b : Fin n := ⟨i,by omega⟩
    let b' : Fin n := ⟨i+1,hi1⟩
    have hbb : (b':ℕ)=b+1 := rfl
    have hstay : orbOf A B (swap b b' * w)=orbOf A B w := by
      have e : gflag n B (swap b b' * w)=gflag n B w :=
        Subtype.ext (by funext p; exact blk_swap B hbb hB (w p))
      unfold orbOf; rw [e]
    have hm : swap b b' * w ∈ D := by simp [D,hstay,hw]
    exact absurd (hmin _ hm) (not_le.mpr (card_invs_swap_left w hbb hd))

/-- Any nonnegative integer matrix with the run margins has a permutation realisation. -/
theorem exists_of_margins {n : ℕ} (A B : Finset ℕ)
    (M : Fin (n+1) → Fin (n+1) → ℕ)
    (hrow : ∀ i, ∑ j,M i j=fib (blk n A) i)
    (hcol : ∀ j, ∑ i,M i j=fib (blk n B) j) :
    ∃ w : Perm (Fin n), descP w ⊆ A ∧ descP w⁻¹ ⊆ B ∧ ofPerm A B w=M := by
  classical
  let K := Fin (n+1) × Fin (n+1)
  let X := Σ p : K, Fin (M p.1 p.2)
  have hc : Fintype.card X=n := by
    dsimp [X,K]
    rw [Fintype.card_sigma]
    simp only [Fintype.card_fin,Fintype.sum_prod_type,hrow]
    have h := Finset.card_eq_sum_card_fiberwise (s := (univ : Finset (Fin n)))
      (t := univ) (f := blk n A) (by intro p _; exact mem_univ _)
    simpa [fib] using h.symm
  let e : Fin n ≃ X := Fintype.equivOfCardEq (by simpa using hc.symm)
  let f : Fin n → Fin (n+1) := fun p => (e p).1.1
  let g : Fin n → Fin (n+1) := fun p => (e p).1.2
  have hcell : cell f g=M := by
    funext i j
    let t : Finset X := univ.filter (fun p => p.1=(i,j))
    have ht : t.card=M i j := by
      have hcM : (univ : Finset (Fin (M i j))).card=M i j := by simp
      conv_rhs => rw [←hcM]
      apply card_bij (s := t) (t := (univ : Finset (Fin (M i j))))
        (fun p hp => ⟨p.2.val,by
          have he := (mem_filter.mp hp).2
          have hh := p.2.is_lt
          simpa [he] using hh⟩)
      · intro p _; exact mem_univ _
      · intro p hp q hq he
        apply Sigma.ext
        · exact (mem_filter.mp hp).2.trans (mem_filter.mp hq).2.symm
        · have hpq : p.1=q.1 := (mem_filter.mp hp).2.trans (mem_filter.mp hq).2.symm
          cases p with
          | mk p v =>
            cases q with
            | mk q z =>
              dsimp at hpq
              subst q
              apply heq_iff_eq.mpr
              exact Fin.ext (congrArg (fun x : Fin (M i j) => x.val) he)
      · intro k _
        refine ⟨⟨(i,j),k⟩,by simp [t],by rfl⟩
    rw [cell,←ht]
    apply card_bij (fun p _ => e p)
    · intro p hp
      simp only [t,mem_filter,mem_univ,true_and,Prod.mk.injEq]
      exact Prod.ext (mem_filter.mp hp).2.1 (mem_filter.mp hp).2.2
    · intro p _ q _ he; exact e.injective he
    · intro p hp
      refine ⟨e.symm p,?_,by simp⟩
      have hh := (mem_filter.mp hp).2
      simp only [mem_filter,mem_univ,true_and,f,g,Equiv.apply_symm_apply]
      exact ⟨congrArg Prod.fst hh,congrArg Prod.snd hh⟩
  let F : Flag n A := ⟨f,fun i => by rw [←row_sum f g i,hcell,hrow]⟩
  let G : Flag n B := ⟨g,fun j => by rw [←col_sum f g j,hcell,hcol]⟩
  obtain ⟨w,hwA,hwB,hw⟩ := exists_monotone_rep A B F G
  refine ⟨w,hwA,hwB,?_⟩
  have he := cell_of_orbit_eq hw
  exact he.trans hcell

/-- Increasing within both sets of runs determines a permutation from its matrix. -/
theorem ofPerm_injective {n : ℕ} (A B : Finset ℕ) (w w' : Perm (Fin n))
    (hwA : descP w ⊆ A) (hwB : descP w⁻¹ ⊆ B)
    (hw'A : descP w' ⊆ A) (hw'B : descP w'⁻¹ ⊆ B)
    (heq : ofPerm A B w = ofPerm A B w') : w=w' := by
  -- the value-block labellings agree
  have hg : ∀ p, blk n B (w p) = blk n B (w' p) := by
    intro p
    set I := univ.filter (fun q => blk n A q = blk n A p)
    have hmono : ∀ (v : Perm (Fin n)), descP v ⊆ A →
        ∀ a ∈ I, ∀ b ∈ I, a ≤ b → (blk n B ∘ v) a ≤ (blk n B ∘ v) b := by
      intro v hv a ha b hb hab
      simp only [I, Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
      rcases eq_or_lt_of_le hab with e | e
      · rw [e]
      · have hbl : block A a = block A b := by
          rw [← blk_val, ← blk_val, ha, hb]
        exact blk_mono B ((descP_subset_iff_blocks v A).mp hv a b hbl e).le
    have hfib : ∀ j, (I.filter (fun q => (blk n B ∘ w) q = j)).card =
        (I.filter (fun q => (blk n B ∘ w') q = j)).card := by
      intro j
      have hh := congrFun (congrFun heq (blk n A p)) j
      simpa [ofPerm,cell,I,filter_filter] using hh
    exact eq_of_monotone_fib I (blk n B ∘ w) (blk n B ∘ w') (hmono w hwA) (hmono w' hw'A) hfib
      (by simp [I])
  -- hence the permutations agree
  have hinv : w⁻¹ = w'⁻¹ := by
    ext v
    congr 1
    set J := univ.filter (fun x => blk n B x = blk n B v)
    have hsm : ∀ (u : Perm (Fin n)), descP u⁻¹ ⊆ B →
        ∀ a ∈ J, ∀ b ∈ J, a < b → u⁻¹ a < u⁻¹ b := by
      intro u hu a ha b hb hab
      simp only [J, Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
      have hbl : block B a = block B b := by rw [← blk_val, ← blk_val, ha, hb]
      exact (descP_subset_iff_blocks u⁻¹ B).mp hu a b hbl hab
    have himg : ∀ (u : Perm (Fin n)),
        J.image ⇑u⁻¹ = univ.filter (fun p => blk n B (u p) = blk n B v) := by
      intro u
      ext p
      simp only [J, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨x, hx, rfl⟩; simpa using hx
      · intro hp; exact ⟨u p, hp, by simp⟩
    have hsame : J.image ⇑w⁻¹ = J.image ⇑w'⁻¹ := by
      rw [himg, himg]
      exact Finset.filter_congr fun p _ => by rw [hg p]
    exact eq_of_strictMono_image J ⇑w⁻¹ ⇑w'⁻¹ (hsm w hwB) (hsm w' hw'B) hsame (by simp [J])
  exact inv_inj.mp hinv
end Contingency
end Stanley.Alt
