/- Two increasing blocks and the binary membership-word model.
The permutation is defined on the original `Fin n`, and all descent sets
are the actual `Stanley.descP` sets. No existence/counting hypothesis. -/
import LeanProofs.Stanley.JointMultiplicity

namespace Stanley
open Finset Equiv

namespace TwoBlocks

def rank {n : ℕ} (A : Finset (Fin n)) (x : Fin n) : ℕ :=
  (A.filter (· < x)).card

theorem rank_lt_card {n : ℕ} {A : Finset (Fin n)} {x : Fin n} (hx : x ∈ A) :
    rank A x < A.card := by
  apply card_lt_card
  refine ⟨filter_subset _ _, ?_⟩
  intro h
  have := h hx
  simpa using this

theorem rank_strict {n : ℕ} {A : Finset (Fin n)} {x y : Fin n}
    (hx : x ∈ A) (hxy : x < y) : rank A x < rank A y := by
  apply card_lt_card
  refine ⟨?_, ?_⟩
  · intro z hz
    exact mem_filter.mpr ⟨(mem_filter.mp hz).1, lt_trans (mem_filter.mp hz).2 hxy⟩
  · intro h
    have := h (mem_filter.mpr ⟨hx, hxy⟩)
    simpa using this

theorem card_add_compl {n : ℕ} (A : Finset (Fin n)) : A.card + Aᶜ.card = n := by
  simpa using Finset.card_add_card_compl A

def position {n : ℕ} (A : Finset (Fin n)) (x : Fin n) : Fin n :=
  if hx : x ∈ A then ⟨rank A x, lt_of_lt_of_le (rank_lt_card hx)
    (by simpa using card_le_univ A)⟩
  else ⟨A.card + rank Aᶜ x, by
    have h := rank_lt_card (mem_compl.mpr hx)
    have := card_add_compl A
    omega⟩

theorem position_val_mem {n : ℕ} {A : Finset (Fin n)} {x : Fin n} (hx : x ∈ A) :
    (position A x : ℕ) = rank A x := by simp [position, hx]

theorem position_val_notMem {n : ℕ} {A : Finset (Fin n)} {x : Fin n} (hx : x ∉ A) :
    (position A x : ℕ) = A.card + rank Aᶜ x := by simp [position, hx]

theorem position_lt_card_iff {n : ℕ} (A : Finset (Fin n)) (x : Fin n) :
    (position A x : ℕ) < A.card ↔ x ∈ A := by
  by_cases hx : x ∈ A
  · simp [position_val_mem hx, hx, rank_lt_card hx]
  · simp [position_val_notMem hx, hx]

theorem position_strict {n : ℕ} {A : Finset (Fin n)} {x y : Fin n}
    (hmem : x ∈ A ↔ y ∈ A) (hxy : x < y) : position A x < position A y := by
  rw [Fin.lt_def]
  by_cases hx : x ∈ A
  · rw [position_val_mem hx, position_val_mem (hmem.mp hx)]
    exact rank_strict hx hxy
  · have hy : y ∉ A := fun h => hx (hmem.mpr h)
    rw [position_val_notMem hx, position_val_notMem hy]
    exact Nat.add_lt_add_left (rank_strict (mem_compl.mpr hx) hxy) _

theorem position_injective {n : ℕ} (A : Finset (Fin n)) : Function.Injective (position A) := by
  intro x y heq
  have hmem : x ∈ A ↔ y ∈ A := by
    rw [← position_lt_card_iff A x, ← position_lt_card_iff A y, heq]
  rcases lt_trichotomy x y with h | h | h
  · exact False.elim ((position_strict hmem h).ne heq)
  · exact h
  · exact False.elim ((position_strict hmem.symm h).ne heq.symm)

noncomputable def sortedPerm {n : ℕ} (A : Finset (Fin n)) : Perm (Fin n) :=
  (Equiv.ofBijective (position A) ((Fintype.bijective_iff_injective_and_card _).mpr
    ⟨position_injective A, rfl⟩)).symm

@[simp] theorem sortedPerm_inv_apply {n : ℕ} (A : Finset (Fin n)) (x : Fin n) :
    (sortedPerm A)⁻¹ x = position A x := rfl

theorem sortedPerm_mem_iff {n : ℕ} (A : Finset (Fin n)) (p : Fin n) :
    sortedPerm A p ∈ A ↔ (p : ℕ) < A.card := by
  rw [← position_lt_card_iff]
  have : position A (sortedPerm A p) = p := (sortedPerm A).symm_apply_apply p
  rw [this]

theorem sortedPerm_strict {n : ℕ} (A : Finset (Fin n)) {p q : Fin n}
    (hmem : (p : ℕ) < A.card ↔ (q : ℕ) < A.card) (hpq : p < q) :
    sortedPerm A p < sortedPerm A q := by
  have hm : sortedPerm A p ∈ A ↔ sortedPerm A q ∈ A := by
    rw [sortedPerm_mem_iff, sortedPerm_mem_iff]; exact hmem
  rcases lt_trichotomy (sortedPerm A p) (sortedPerm A q) with h | h | h
  · exact h
  · have := (sortedPerm A).injective h
    exact False.elim (hpq.ne this)
  · have hh := position_strict hm.symm h
    have ep : position A (sortedPerm A p) = p := (sortedPerm A).symm_apply_apply p
    have eq : position A (sortedPerm A q) = q := (sortedPerm A).symm_apply_apply q
    rw [ep, eq] at hh
    exact False.elim (lt_asymm hpq hh)

theorem sortedPerm_desc_subset {n : ℕ} (A : Finset (Fin n)) :
    descP (sortedPerm A) ⊆ {A.card - 1} := by
  intro i hi
  obtain ⟨hn, hd⟩ := Alt.mem_descP.mp hi
  by_contra hnot
  have hne : i ≠ A.card - 1 := by simpa using hnot
  have hm : i < A.card ↔ i + 1 < A.card := by omega
  have hh := sortedPerm_strict A (p := ⟨i, by omega⟩) (q := ⟨i+1, hn⟩)
    hm (by simp)
  exact lt_asymm hh hd

def rises {n : ℕ} (A : Finset (Fin n)) : Finset ℕ :=
  (range (n-1)).filter (fun i => ∃ h : i+1<n,
    (⟨i, by omega⟩ : Fin n) ∉ A ∧ (⟨i+1,h⟩ : Fin n) ∈ A)

theorem inverse_desc_eq_rises {n : ℕ} (A : Finset (Fin n)) :
    descP (sortedPerm A)⁻¹ = rises A := by
  ext i
  simp only [descP, rises, mem_filter, mem_range]
  constructor
  · rintro ⟨hi, hn, hd⟩
    refine ⟨hi, hn, ?_⟩
    rw [sortedPerm_inv_apply, sortedPerm_inv_apply] at hd
    have hi' : i < n := by omega
    have hlt : (⟨i, hi'⟩ : Fin n) < ⟨i+1, hn⟩ := by simp
    by_cases h0 : (⟨i, hi'⟩ : Fin n) ∈ A
    · by_cases h1 : (⟨i+1, hn⟩ : Fin n) ∈ A
      · exact False.elim (lt_asymm (position_strict (by simp [h0,h1]) hlt) hd)
      · have hlow := (position_lt_card_iff A ⟨i, hi'⟩).mpr h0
        have hhigh := (position_lt_card_iff A ⟨i+1, hn⟩).not.mpr h1
        rw [Fin.lt_def] at hd
        omega
    · by_cases h1 : (⟨i+1, hn⟩ : Fin n) ∈ A
      · exact ⟨h0,h1⟩
      · exact False.elim (lt_asymm (position_strict (by simp [h0,h1]) hlt) hd)
  · rintro ⟨hi,hn,h0,h1⟩
    refine ⟨hi,hn,?_⟩
    rw [sortedPerm_inv_apply, sortedPerm_inv_apply, Fin.lt_def]
    have hlow := (position_lt_card_iff A ⟨i+1, hn⟩).mpr h1
    have hhigh := (position_lt_card_iff A ⟨i, by omega⟩).not.mpr h0
    omega

theorem descP_empty_iff {n : ℕ} (w : Perm (Fin n)) : descP w = ∅ ↔ w = 1 := by
  constructor
  · intro hd
    have hm := (Alt.descP_subset_iff_blocks w ∅).mp (by rw [hd])
    have he : w = (1 : Perm (Fin n)) := by
      apply Equiv.ext
      intro p
      exact Alt.eq_of_strictMono_image univ w (1 : Perm (Fin n))
        (fun a _ b _ h => hm a b (by simp [Alt.block]) h)
        (fun a _ b _ h => h) (by simp) (mem_univ p)
    exact he
  · rintro rfl
    ext i
    simp [descP]

theorem sortedPerm_desc_eq {n : ℕ} (A : Finset (Fin n)) (h : (rises A).Nonempty) :
    descP (sortedPerm A) = {A.card-1} := by
  have hd := sortedPerm_desc_subset A
  have hne : descP (sortedPerm A) ≠ ∅ := by
    intro he
    have hw := (descP_empty_iff _).mp he
    have hr := inverse_desc_eq_rises A
    rw [hw] at hr
    have : descP ((1 : Perm (Fin n))⁻¹) = ∅ := by
      simpa using (descP_empty_iff (1 : Perm (Fin n))).mpr rfl
    rw [this] at hr
    exact h.ne_empty hr.symm
  exact Finset.eq_singleton_iff_nonempty_unique_mem.mpr
    ⟨Finset.nonempty_iff_ne_empty.mpr hne, fun i hi => mem_singleton.mp (hd hi)⟩

theorem rank_eq_index {n : ℕ} (A : Finset (Fin n)) (x : A) :
    rank A x = ((A.orderIsoOfFin rfl).symm x : ℕ) := by
  let e := A.orderIsoOfFin rfl
  have hs : A.filter (· < x.1) = (Finset.Iio (e.symm x)).map
      ⟨fun i => (e i).1, fun i j h => e.injective (Subtype.ext h)⟩ := by
    ext y
    simp only [mem_filter, mem_map, mem_Iio]
    constructor
    · rintro ⟨hy, hlt⟩
      refine ⟨e.symm ⟨y,hy⟩, e.symm.lt_iff_lt.mpr hlt, ?_⟩
      exact congrArg Subtype.val (e.apply_symm_apply ⟨y,hy⟩)
    · rintro ⟨i,hi,rfl⟩
      refine ⟨(e i).2, ?_⟩
      have := e.lt_iff_lt.mpr hi
      rw [OrderIso.apply_symm_apply] at this
      exact this
  change (A.filter (· < x.1)).card = _
  rw [hs,card_map,Fin.card_Iio]

theorem card_filter_rank {n : ℕ} (A : Finset (Fin n)) (m : ℕ) (hm : m ≤ A.card) :
    (A.filter (fun x => rank A x < m)).card = m := by
  let e := A.orderIsoOfFin rfl
  conv_rhs => rw [← card_range m]
  apply Finset.card_bij (t := range m)
    (fun x hx => ((e.symm ⟨x,(mem_filter.mp hx).1⟩) : ℕ))
  · intro x hx
    rw [mem_range, ← rank_eq_index A ⟨x,(mem_filter.mp hx).1⟩]
    exact (mem_filter.mp hx).2
  · intro x hx y hy h
    have he : e.symm ⟨x,(mem_filter.mp hx).1⟩ = e.symm ⟨y,(mem_filter.mp hy).1⟩ := Fin.ext h
    exact congrArg Subtype.val (e.symm.injective he)
  · intro i hi
    have him : i < m := mem_range.mp hi
    let j : Fin A.card := ⟨i,lt_of_lt_of_le him hm⟩
    refine ⟨(e j).1, ?_, ?_⟩
    · refine mem_filter.mpr ⟨(e j).2, ?_⟩
      rw [rank_eq_index]
      simpa [e,j] using him
    · change ((e.symm (e j)) : ℕ) = i
      rw [OrderIso.symm_apply_apply]

theorem rises_separated {n : ℕ} (A : Finset (Fin n)) :
    ∀ i ∈ rises A, i+1 ∉ rises A := by
  intro i hi hi'
  obtain ⟨_,hn,h0,h1⟩ := mem_filter.mp hi
  obtain ⟨_,hn',h0',h1'⟩ := mem_filter.mp hi'
  exact h0' h1

theorem rises_card_le {n : ℕ} (A : Finset (Fin n)) :
    (rises A).card ≤ A.card ∧ (rises A).card ≤ Aᶜ.card := by
  let f : rises A → A := fun i => ⟨⟨i.1+1,(mem_filter.mp i.2).2.choose⟩,
    (mem_filter.mp i.2).2.choose_spec.2⟩
  let g : rises A → ↥(Aᶜ) := fun i => ⟨⟨i.1,by
    have := (mem_filter.mp i.2).2.choose; omega⟩,
    mem_compl.mpr (mem_filter.mp i.2).2.choose_spec.1⟩
  constructor
  · have h := Fintype.card_le_of_injective f (by
      intro i j h
      apply Subtype.ext
      have := congrArg (fun x : A => (x.1 : ℕ)) h
      change i.1+1=j.1+1 at this
      omega)
    simpa using h
  · have h := Fintype.card_le_of_injective g (by
      intro i j h
      apply Subtype.ext
      exact congrArg (fun x : ↥(Aᶜ) => (x.1 : ℕ)) h)
    simpa only [Fintype.card_coe] using h

def initialValues {n : ℕ} (w : Perm (Fin n)) (a : ℕ) : Finset (Fin n) :=
  univ.filter (fun x => (w⁻¹ x : ℕ) < a)

theorem card_initialValues {n : ℕ} (w : Perm (Fin n)) (a : ℕ) (ha : a ≤ n) :
    (initialValues w a).card = a := by
  conv_rhs => rw [← card_range a]
  apply Finset.card_bij (t := range a) (fun x _ => (w⁻¹ x : ℕ))
  · intro x hx
    exact mem_range.mpr (mem_filter.mp hx).2
  · intro x _ y _ h
    exact w⁻¹.injective (Fin.ext h)
  · intro i hi
    have hin : i < n := lt_of_lt_of_le (mem_range.mp hi) ha
    refine ⟨w ⟨i,hin⟩, ?_, ?_⟩ <;> simp [initialValues,mem_range.mp hi]

theorem initialValues_sortedPerm {n : ℕ} (A : Finset (Fin n)) :
    initialValues (sortedPerm A) A.card = A := by
  apply Finset.ext
  intro x
  simp only [initialValues, Finset.mem_filter, Finset.mem_univ, true_and]
  exact position_lt_card_iff A x

theorem block_singleton (a i : ℕ) (ha : 0<a) :
    Alt.block {a-1} i = if a ≤ i then 1 else 0 := by
  simp only [Alt.block,filter_singleton]
  split_ifs <;> simp_all <;> omega

theorem eq_sortedPerm_initialValues {n : ℕ} (w : Perm (Fin n)) (a : ℕ)
    (ha : 0<a) (han : a≤n) (hw : descP w ⊆ {a-1}) :
    w = sortedPerm (initialValues w a) := by
  let A := initialValues w a
  have hc : A.card=a := card_initialValues w a han
  have hm := (Alt.descP_subset_iff_blocks w {a-1}).mp hw
  have hmem : ∀ p, w p ∈ A ↔ sortedPerm A p ∈ A := by
    intro p
    rw [sortedPerm_mem_iff,hc]
    simp [A,initialValues]
  apply Equiv.ext
  intro p
  let I := univ.filter (fun q : Fin n => (q : ℕ)<a ↔ (p : ℕ)<a)
  have heq : I.image w = I.image (sortedPerm A) := by
    ext x
    simp only [mem_image]
    constructor
    · rintro ⟨q,hq,rfl⟩
      refine ⟨(sortedPerm A)⁻¹ (w q), ?_, (sortedPerm A).apply_symm_apply _⟩
      have hh := hmem ((sortedPerm A)⁻¹ (w q))
      have hv : w q ∈ A ↔ (q : ℕ)<a := by simp [A,initialValues]
      have hv' := sortedPerm_mem_iff A ((sortedPerm A)⁻¹ (w q))
      have he : sortedPerm A ((sortedPerm A)⁻¹ (w q)) = w q := (sortedPerm A).apply_symm_apply _
      rw [he,hc] at hv'
      simp only [I,mem_filter,mem_univ,true_and] at hq ⊢
      exact hv'.symm.trans (hv.trans hq)
    · rintro ⟨q,hq,rfl⟩
      refine ⟨w⁻¹ (sortedPerm A q), ?_, by simp⟩
      have hv : sortedPerm A q ∈ A ↔ ((w⁻¹ (sortedPerm A q) : Fin n) : ℕ)<a := by
        simp [A,initialValues]
      have hv' := sortedPerm_mem_iff A q
      rw [hc] at hv'
      simp only [I,mem_filter,mem_univ,true_and] at hq ⊢
      exact hv.symm.trans (hv'.trans hq)
  exact Alt.eq_of_strictMono_image I w (sortedPerm A)
    (fun x hx y hy hxy => hm x y (by
      simp only [I,mem_filter,mem_univ,true_and] at hx hy
      have hboth : ((x : ℕ)<a) ↔ ((y : ℕ)<a) := hx.trans hy.symm
      rw [block_singleton a x ha,block_singleton a y ha]
      split_ifs <;> omega) hxy)
    (fun x hx y hy hxy => sortedPerm_strict A (by
      rw [hc]
      exact (mem_filter.mp hx).2.trans (mem_filter.mp hy).2.symm) hxy)
    heq (by simp [I])

end TwoBlocks
end Stanley

