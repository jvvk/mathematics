/-
  Part B. Rank matching. Given marked positions `P` and marked values `V` (subsets of
  `{0, …, n-1}` of equal size), a pivot `p ∈ P`, `v ∈ V`, and the two counting conditions
    #{q ∈ P | q < p} = #{x ∈ V | v < x},   #{q ∉ P | q < p} = #{x ∉ V | x < v},
  the map sending the r-th smallest marked position to the r-th largest marked value, and the
  r-th smallest unmarked position to the r-th smallest unmarked value, is a `Good` bijection.
-/
import LeanProofs.Stanley.Descent

namespace Stanley

open Finset

/-- The rank of `x` in `s` is the number of elements of `s` below it. -/
theorem rank_eq {s : Finset ℕ} {m : ℕ} (e : Fin m ≃o s) (x : s) :
    (s.filter (· < x.1)).card = (e.symm x : ℕ) := by
  have hset : s.filter (· < x.1) =
      (Finset.Iio (e.symm x)).map ⟨fun i => (e i).1, fun i j h => e.injective (Subtype.ext h)⟩ := by
    ext y
    simp only [Finset.mem_filter, Finset.mem_map, Finset.mem_Iio]
    constructor
    · rintro ⟨hy, hlt⟩
      refine ⟨e.symm ⟨y, hy⟩, ?_, ?_⟩
      swap
      · show (e (e.symm ⟨y, hy⟩)).1 = y
        rw [OrderIso.apply_symm_apply]
      exact e.symm.lt_iff_lt.mpr (Subtype.mk_lt_mk.mpr hlt)
    · rintro ⟨i, hi, rfl⟩
      refine ⟨(e i).2, ?_⟩
      have := e.lt_iff_lt.mpr hi
      rw [OrderIso.apply_symm_apply] at this
      exact this
  rw [hset, Finset.card_map, Fin.card_Iio]

/-- `x < y` iff the rank of `x` is below the number of elements of `s` below `y`. -/
theorem lt_iff_rank_lt {s : Finset ℕ} {m : ℕ} (e : Fin m ≃o s) (x : s) (y : ℕ) :
    x.1 < y ↔ (e.symm x : ℕ) < (s.filter (· < y)).card := by
  rw [← rank_eq e x]
  constructor
  · intro h
    apply Finset.card_lt_card
    refine ⟨fun z hz => ?_, fun hsub => ?_⟩
    · simp only [Finset.mem_filter] at hz ⊢; exact ⟨hz.1, lt_trans hz.2 h⟩
    · have := hsub (Finset.mem_filter.mpr ⟨x.2, h⟩)
      simp at this
  · intro h
    by_contra hge
    push Not at hge
    have : (s.filter (· < y)) ⊆ (s.filter (· < x.1)) := by
      intro z hz
      simp only [Finset.mem_filter] at hz ⊢
      exact ⟨hz.1, lt_of_lt_of_le hz.2 hge⟩
    exact absurd (Finset.card_le_card this) (not_le.mpr h)

/-- Elements below, the element, and elements above partition `s`. -/
theorem card_split {s : Finset ℕ} {x : ℕ} (hx : x ∈ s) :
    (s.filter (· < x)).card + (s.filter (x < ·)).card + 1 = s.card := by
  have h1 := Finset.card_filter_add_card_filter_not (s := s) (p := fun y => y < x)
  have h2 := Finset.card_filter_add_card_filter_not (s := s.filter (fun y => ¬ y < x))
    (p := fun y => x < y)
  have h3 : (s.filter (fun y => ¬ y < x)).filter (fun y => x < y) = s.filter (x < ·) := by
    ext y; simp only [Finset.mem_filter]; constructor
    · rintro ⟨⟨h, _⟩, h'⟩; exact ⟨h, h'⟩
    · rintro ⟨h, h'⟩; exact ⟨⟨h, by omega⟩, h'⟩
  have h4 : (s.filter (fun y => ¬ y < x)).filter (fun y => ¬ x < y) = {x} := by
    ext y; simp only [Finset.mem_filter, Finset.mem_singleton]; constructor
    · rintro ⟨⟨_, h⟩, h'⟩; omega
    · rintro rfl; exact ⟨⟨hx, lt_irrefl _⟩, lt_irrefl _⟩
  rw [h3, h4, Finset.card_singleton] at h2
  omega

section Build

variable (n m m' : ℕ) (P V : Finset ℕ) (hP : P.card = m) (hV : V.card = m)
  (hPc : (range n \ P).card = m') (hVc : (range n \ V).card = m')

/-- Rank matching: marked positions to marked values reversing order, unmarked positions to
unmarked values preserving order, identity outside `{0, …, n-1}`. -/
noncomputable def rmatch (q : ℕ) : ℕ :=
  if hq : q ∈ P then (V.orderIsoOfFin hV (Fin.rev ((P.orderIsoOfFin hP).symm ⟨q, hq⟩))).1
  else if hq' : q ∈ range n \ P then
    ((range n \ V).orderIsoOfFin hVc (((range n \ P).orderIsoOfFin hPc).symm ⟨q, hq'⟩)).1
  else q

variable {n m m' P V}

theorem rmatch_of_mem (hq : q ∈ P) : rmatch n m m' P V hP hV hPc hVc q =
    (V.orderIsoOfFin hV (Fin.rev ((P.orderIsoOfFin hP).symm ⟨q, hq⟩))).1 := by
  unfold rmatch; rw [dif_pos hq]

theorem rmatch_of_mem_c (hq : q ∈ range n \ P) : rmatch n m m' P V hP hV hPc hVc q =
    ((range n \ V).orderIsoOfFin hVc (((range n \ P).orderIsoOfFin hPc).symm ⟨q, hq⟩)).1 := by
  unfold rmatch; rw [dif_neg (Finset.mem_sdiff.mp hq).2, dif_pos hq]

theorem rmatch_mem (hq : q ∈ P) : rmatch n m m' P V hP hV hPc hVc q ∈ V := by
  rw [rmatch_of_mem hP hV hPc hVc hq]; exact Subtype.property _

theorem rmatch_mem_c (hq : q ∈ range n \ P) : rmatch n m m' P V hP hV hPc hVc q ∈ range n \ V := by
  rw [rmatch_of_mem_c hP hV hPc hVc hq]; exact Subtype.property _

theorem rmatch_inv (hq : q ∈ P) :
    rmatch n m m' V P hV hP hVc hPc (rmatch n m m' P V hP hV hPc hVc q) = q := by
  have hx := rmatch_mem hP hV hPc hVc hq
  rw [rmatch_of_mem hV hP hVc hPc hx]
  have hsub : (⟨rmatch n m m' P V hP hV hPc hVc q, hx⟩ : V) =
      V.orderIsoOfFin hV (Fin.rev ((P.orderIsoOfFin hP).symm ⟨q, hq⟩)) :=
    Subtype.ext (rmatch_of_mem hP hV hPc hVc hq)
  rw [hsub, OrderIso.symm_apply_apply, Fin.rev_rev, OrderIso.apply_symm_apply]

theorem rmatch_inv_c (hq : q ∈ range n \ P) :
    rmatch n m m' V P hV hP hVc hPc (rmatch n m m' P V hP hV hPc hVc q) = q := by
  have hx := rmatch_mem_c hP hV hPc hVc hq
  rw [rmatch_of_mem_c hV hP hVc hPc hx]
  have hsub : (⟨rmatch n m m' P V hP hV hPc hVc q, hx⟩ : ↥(range n \ V)) =
      (range n \ V).orderIsoOfFin hVc (((range n \ P).orderIsoOfFin hPc).symm ⟨q, hq⟩) :=
    Subtype.ext (rmatch_of_mem_c hP hV hPc hVc hq)
  rw [hsub, OrderIso.symm_apply_apply, OrderIso.apply_symm_apply]


theorem rmatch_lt_iff (hq : q ∈ P) (hq' : q' ∈ P) :
    rmatch n m m' P V hP hV hPc hVc q < rmatch n m m' P V hP hV hPc hVc q' ↔ q' < q := by
  rw [rmatch_of_mem hP hV hPc hVc hq, rmatch_of_mem hP hV hPc hVc hq', Subtype.coe_lt_coe,
    OrderIso.lt_iff_lt, Fin.rev_lt_rev, OrderIso.lt_iff_lt, Subtype.mk_lt_mk]

theorem rmatch_lt_iff_c (hq : q ∈ range n \ P) (hq' : q' ∈ range n \ P) :
    rmatch n m m' P V hP hV hPc hVc q < rmatch n m m' P V hP hV hPc hVc q' ↔ q < q' := by
  rw [rmatch_of_mem_c hP hV hPc hVc hq, rmatch_of_mem_c hP hV hPc hVc hq', Subtype.coe_lt_coe,
    OrderIso.lt_iff_lt, OrderIso.lt_iff_lt, Subtype.mk_lt_mk]

/-- Under the two counting conditions the rank matching is `Good`. -/
theorem rmatch_good {p v : ℕ} (hpP : p ∈ P) (hvV : v ∈ V)
    (hA : (P.filter (· < p)).card = (V.filter (v < ·)).card)
    (hD : ((range n \ P).filter (· < p)).card = ((range n \ V).filter (· < v)).card) :
    Good n (rmatch n m m' P V hP hV hPc hVc) P p v := by
  have hwp : rmatch n m m' P V hP hV hPc hVc p = v := by
    rw [rmatch_of_mem hP hV hPc hVc hpP]
    have hfin : Fin.rev ((P.orderIsoOfFin hP).symm ⟨p, hpP⟩) = (V.orderIsoOfFin hV).symm ⟨v, hvV⟩ := by
      apply Fin.ext
      rw [Fin.val_rev, ← rank_eq (P.orderIsoOfFin hP), ← rank_eq (V.orderIsoOfFin hV)]
      have h1 := card_split hvV
      have h2 := card_split hpP
      simp only at h1 h2 ⊢
      omega
    rw [hfin, OrderIso.apply_symm_apply]
  refine ⟨hpP, hwp, ?_, ?_, ?_, ?_⟩
  · intro q hq q' hq' hlt
    exact (rmatch_lt_iff hP hV hPc hVc hq' hq).mpr hlt
  · intro q hqn q' hqn' hq hq' hlt
    exact (rmatch_lt_iff_c hP hV hPc hVc (Finset.mem_sdiff.mpr ⟨Finset.mem_range.mpr hqn, hq⟩)
      (Finset.mem_sdiff.mpr ⟨Finset.mem_range.mpr hqn', hq'⟩)).mpr hlt
  · intro q hq
    rw [← hwp]
    exact (rmatch_lt_iff hP hV hPc hVc hpP hq).symm
  · intro q hqn hq
    have hqc : q ∈ range n \ P := Finset.mem_sdiff.mpr ⟨Finset.mem_range.mpr hqn, hq⟩
    have hx := rmatch_mem_c hP hV hPc hVc hqc
    rw [lt_iff_rank_lt ((range n \ P).orderIsoOfFin hPc) ⟨q, hqc⟩ p, hD]
    have := lt_iff_rank_lt ((range n \ V).orderIsoOfFin hVc)
      ⟨rmatch n m m' P V hP hV hPc hVc q, hx⟩ v
    rw [this]
    have hsub : (⟨rmatch n m m' P V hP hV hPc hVc q, hx⟩ : ↥(range n \ V)) =
        (range n \ V).orderIsoOfFin hVc (((range n \ P).orderIsoOfFin hPc).symm ⟨q, hqc⟩) :=
      Subtype.ext (rmatch_of_mem_c hP hV hPc hVc hqc)
    rw [hsub, OrderIso.symm_apply_apply]

end Build

end Stanley
