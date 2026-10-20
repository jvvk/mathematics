import LeanProofs.Precarious.Framework

/-!
# Precarious necklaces (MO 515996): the closed form, lower bound

Keeping any `s` of `k` colours (`1 ≤ s < k`) symmetric forces
`|w| ≥ s · p_{⌊s/2⌋+1}# + (k - s) · p_{⌈s/2⌉}#` (`keep_general_bound`).

Route. Each prime `q` used on kept sets has an *avoided pair* `e q` that none of its sets contains
(`keep_framework`). For a colour `x`, let `Px x` be the primes on kept sets through `x`. The avoided pairs of
`Px x`, with `x`, span at least `s + 1` colours (`span`), so `x` sees at least `⌈s/2⌉` primes and its count is
at least `p_{|Px x|}#`. For odd `s` that is already `⌊s/2⌋ + 1`. For even `s = 2h`, a colour seeing only `h`
primes (light) has `h` disjoint avoided pairs covering `2h` colours outside it. For `y` in one pair with
partner `z`, erasing `z` from the `2h + 1` colours leaves a kept set through `x` and `y` that contains every
other pair, so its prime is `y`'s own and `y` sees a prime whose pair contains it: `y` sees `h + 1` primes.
-/

set_option linter.unusedSectionVars false

namespace Precarious

open Finset

variable {α : Type*} [DecidableEq α]

/-- The formula. -/
noncomputable def closedForm (k s : ℕ) : ℕ := s * pr (s / 2 + 1) + (k - s) * pr ((s + 1) / 2)

theorem keep_general_bound (s : ℕ) (hs1 : 1 ≤ s) (w : List α) (hw : KeepPrec s w)
    (hsk : s < w.toFinset.card) : closedForm w.toFinset.card s ≤ w.length := by
  classical
  set C := w.toFinset with hC
  obtain ⟨c, hcp, hdvd, hcov⟩ := keep_framework s w hw (by rw [← hC]; omega)
  choose eu heu ev hev hne havoid using hcov
  -- the avoided pair of each prime
  let e : ℕ → Finset α := fun q => {eu q, ev q}
  have he2 : ∀ q, (e q).card = 2 := fun q => card_pair (hne q)
  have heC : ∀ q, e q ⊆ C := by
    intro q z hz
    simp only [e, mem_insert, mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact List.mem_toFinset.mpr (heu q)
    · exact List.mem_toFinset.mpr (hev q)
  have hav : ∀ S ⊆ C, S.card = s → ¬ e (c S) ⊆ S := by
    intro S hSC hSs hsub
    exact havoid (c S) S hSC hSs rfl ⟨hsub (by simp [e]), hsub (by simp [e])⟩
  -- kept sets through `x`, and their primes
  let K : α → Finset (Finset α) := fun x => (C.powersetCard s).filter (fun S => x ∈ S)
  let Px : α → Finset ℕ := fun x => (K x).image c
  have memK : ∀ x S, S ∈ K x ↔ S ⊆ C ∧ S.card = s ∧ x ∈ S := by
    intro x S; simp [K, mem_powersetCard, and_assoc]
  -- the avoided pairs of `Px x`, with `x`, span `s + 1` colours
  have span : ∀ x ∈ C, s + 1 ≤ (insert x ((Px x).biUnion e)).card := by
    intro x hxC
    by_contra hlt
    push Not at hlt
    have hTC : insert x ((Px x).biUnion e) ⊆ C := by
      intro z hz
      rcases mem_insert.mp hz with rfl | hz
      · exact hxC
      · obtain ⟨q, _, hzq⟩ := mem_biUnion.mp hz; exact heC q hzq
    obtain ⟨S, hTS, hSC, hSs⟩ := exists_subsuperset_card_eq hTC (by omega) hsk.le
    have hSK : S ∈ K x := (memK x S).mpr ⟨hSC, hSs, hTS (mem_insert_self x _)⟩
    apply hav S hSC hSs
    intro z hz
    exact hTS (mem_insert_of_mem (mem_biUnion.mpr ⟨c S, mem_image_of_mem c hSK, hz⟩))
  have hbi : ∀ x, ((Px x).biUnion e).card ≤ 2 * (Px x).card := by
    intro x
    refine (card_biUnion_le).trans ?_
    rw [mul_comm, ← smul_eq_mul, ← sum_const]
    exact sum_le_sum (fun q _ => (he2 q).le)
  have hlow : ∀ x ∈ C, s ≤ 2 * (Px x).card := by
    intro x hxC
    have := span x hxC
    have := (card_insert_le x ((Px x).biUnion e)).trans (Nat.add_le_add_right (hbi x) 1)
    omega
  -- each count is at least the product of the first `|Px x|` primes
  have hcount : ∀ x ∈ C, pr (Px x).card ≤ w.count x := by
    intro x hxC
    have hpos : 0 < w.count x := List.count_pos_iff.mpr (List.mem_toFinset.mp hxC)
    refine (prod_ge_pr (Px x) ?_).trans (Nat.le_of_dvd hpos (Finset.prod_primes_dvd _ ?_ ?_))
    · intro q hq; obtain ⟨S, _, rfl⟩ := mem_image.mp hq; exact hcp S
    · intro q hq; obtain ⟨S, _, rfl⟩ := mem_image.mp hq; exact (hcp S).prime
    · intro q hq
      obtain ⟨S, hS, rfl⟩ := mem_image.mp hq
      obtain ⟨hSC, hSs, hxS⟩ := (memK x S).mp hS
      exact hdvd S hSC hSs x hxS
  have hlen : w.length = ∑ x ∈ C, w.count x := (List.sum_toFinset_count_eq_length w).symm
  have hk : C.card = w.toFinset.card := rfl
  rcases Nat.even_or_odd s with ⟨h, hh⟩ | ⟨h, hh⟩
  · -- even `s = 2h`
    have hs2 : s / 2 + 1 = h + 1 := by omega
    have hs3 : (s + 1) / 2 = h := by omega
    unfold closedForm
    rw [← hk, hs2, hs3, hlen]
    -- heavy: sees a prime whose avoided pair contains it
    have heavy : ∀ y ∈ C, (∃ S ∈ K y, y ∈ e (c S)) → h + 1 ≤ (Px y).card := by
      rintro y hyC ⟨S, hSK, hyS⟩
      have hyU : y ∈ (Px y).biUnion e := mem_biUnion.mpr ⟨c S, mem_image_of_mem c hSK, hyS⟩
      have := span y hyC
      rw [insert_eq_of_mem hyU] at this
      have := hbi y
      omega
    by_cases hlight : ∃ x ∈ C, (Px x).card ≤ h
    · obtain ⟨x, hxC, hxh⟩ := hlight
      set E := (Px x).biUnion e with hE
      have hxh' : (Px x).card = h := le_antisymm hxh (by have := hlow x hxC; omega)
      have hV : s + 1 ≤ (insert x E).card := span x hxC
      have hEle : E.card ≤ 2 * (Px x).card := hbi x
      have hxE : x ∉ E := by
        intro hxE; rw [insert_eq_of_mem hxE] at hV; omega
      have hEcard : E.card = s := by
        rw [card_insert_of_notMem hxE] at hV; omega
      have hEC : E ⊆ C := by
        intro z hz; obtain ⟨q, _, hzq⟩ := mem_biUnion.mp hz; exact heC q hzq
      set V := insert x E with hVdef
      have hVC : V ⊆ C := insert_subset hxC hEC
      have hVcard : V.card = s + 1 := by rw [hVdef, card_insert_of_notMem hxE, hEcard]
      -- erasing `y ∈ E` leaves a kept set through `x`
      let Sy : α → Finset α := fun y => V.erase y
      have hSyK : ∀ y ∈ E, Sy y ∈ K x := by
        intro y hy
        refine (memK x _).mpr ⟨(erase_subset _ _).trans hVC, ?_, ?_⟩
        · rw [card_erase_of_mem (mem_insert_of_mem hy), hVcard]; omega
        · exact mem_erase.mpr ⟨fun h => hxE (h ▸ hy), mem_insert_self x E⟩
      -- the `h` avoided pairs are disjoint, since together they cover `2h` colours
      have hdisj : ∀ q ∈ Px x, ∀ q' ∈ Px x, q ≠ q' → Disjoint (e q) (e q') := by
        intro q hq q' hq' hqq'
        rw [disjoint_iff_ne]
        rintro z hz _ hz' rfl
        have hsub : E ⊆ (e q ∪ e q') ∪ (((Px x).erase q).erase q').biUnion e := by
          intro u hu
          obtain ⟨r, hr, hur⟩ := mem_biUnion.mp hu
          by_cases hrq : r = q
          · subst hrq; exact mem_union_left _ (mem_union_left _ hur)
          by_cases hrq' : r = q'
          · subst hrq'; exact mem_union_left _ (mem_union_right _ hur)
          exact mem_union_right _ (mem_biUnion.mpr ⟨r, mem_erase.mpr ⟨hrq', mem_erase.mpr ⟨hrq, hr⟩⟩, hur⟩)
        have hun : (e q ∪ e q').card ≤ 3 := by
          have hi : 1 ≤ (e q ∩ e q').card := card_pos.mpr ⟨z, mem_inter.mpr ⟨hz, hz'⟩⟩
          have := card_union_add_card_inter (e q) (e q')
          rw [he2, he2] at this; omega
        have hrest : ((((Px x).erase q).erase q').biUnion e).card ≤ 2 * (h - 2) := by
          refine (card_biUnion_le).trans ?_
          have hc : (((Px x).erase q).erase q').card = h - 2 := by
            rw [card_erase_of_mem (mem_erase.mpr ⟨Ne.symm hqq', hq'⟩), card_erase_of_mem hq, hxh']
            omega
          rw [mul_comm, ← hc, ← smul_eq_mul, ← sum_const]
          exact sum_le_sum (fun r _ => (he2 r).le)
        have h2 : 2 ≤ h := by
          have := (card_le_card (insert_subset_iff.mpr ⟨hq', singleton_subset_iff.mpr hq⟩ : ({q', q} : Finset ℕ) ⊆ Px x))
          rw [card_pair (Ne.symm hqq'), hxh'] at this; exact this
        have := (card_le_card hsub).trans (card_union_le _ _)
        omega
      -- so every colour of `E` is heavy: erase its partner `z`, and only its own prime fits
      have hEheavy : ∀ y ∈ E, h + 1 ≤ (Px y).card := by
        intro y hy
        obtain ⟨q, hq, hyq⟩ := mem_biUnion.mp hy
        obtain ⟨z, hz, hzy⟩ : ∃ z ∈ e q, z ≠ y := by
          by_contra hno; push Not at hno
          have : e q ⊆ {y} := fun z hz => mem_singleton.mpr (hno z hz)
          have := card_le_card this; rw [he2] at this; simp at this
        have hzE : z ∈ E := mem_biUnion.mpr ⟨q, hq, hz⟩
        obtain ⟨hSC, hSs, _⟩ := (memK x _).mp (hSyK z hzE)
        have hcP : c (Sy z) ∈ Px x := mem_image_of_mem c (hSyK z hzE)
        -- the avoided pair of `Sy z` lies in `V` but not in `V \ {z}`, so it contains `z`
        have hzc : z ∈ e (c (Sy z)) := by
          by_contra hz'
          apply hav (Sy z) hSC hSs
          intro u hu
          exact mem_erase.mpr ⟨fun h => hz' (h ▸ hu),
            mem_insert_of_mem (mem_biUnion.mpr ⟨c (Sy z), hcP, hu⟩)⟩
        have hcq : c (Sy z) = q := by
          by_contra hne
          exact disjoint_left.mp (hdisj _ hcP q hq hne) hzc hz
        apply heavy y (hEC hy)
        refine ⟨Sy z, (memK y _).mpr ⟨hSC, hSs, mem_erase.mpr ⟨Ne.symm hzy, mem_insert_of_mem hy⟩⟩, ?_⟩
        rw [hcq]; exact hyq
      -- sum over `E` and the rest
      rw [← sum_sdiff hEC]
      have h1 : s * pr (h + 1) ≤ ∑ y ∈ E, w.count y := by
        rw [← hEcard, ← smul_eq_mul, ← sum_const]
        exact sum_le_sum (fun y hy => (pr_mono (hEheavy y hy)).trans (hcount y (hEC hy)))
      have h2 : (C.card - s) * pr h ≤ ∑ y ∈ C \ E, w.count y := by
        rw [← hEcard, ← card_sdiff_of_subset hEC, ← smul_eq_mul, ← sum_const]
        refine sum_le_sum (fun y hy => ?_)
        have hyC := (mem_sdiff.mp hy).1
        exact (pr_mono (by have := hlow y hyC; omega)).trans (hcount y hyC)
      omega
    · push Not at hlight
      have h1 : C.card * pr (h + 1) ≤ ∑ x ∈ C, w.count x := by
        rw [← smul_eq_mul, ← sum_const]
        exact sum_le_sum (fun x hx => (pr_mono (hlight x hx)).trans (hcount x hx))
      have h2 : s * pr (h + 1) + (C.card - s) * pr h ≤ C.card * pr (h + 1) := by
        have : pr h ≤ pr (h + 1) := pr_mono (Nat.le_succ h)
        have e1 : C.card * pr (h + 1) = s * pr (h + 1) + (C.card - s) * pr (h + 1) := by
          rw [← add_mul, Nat.add_sub_cancel' hsk.le]
        rw [e1]; exact Nat.add_le_add_left (Nat.mul_le_mul_left _ this) _
      omega
  · -- odd `s = 2h + 1`: every colour sees `h + 1` primes
    have hs2 : s / 2 + 1 = h + 1 := by omega
    have hs3 : (s + 1) / 2 = h + 1 := by omega
    unfold closedForm
    rw [← hk, hs2, hs3, ← add_mul, Nat.add_sub_cancel' hsk.le, hlen, ← smul_eq_mul, ← sum_const]
    exact sum_le_sum (fun x hx => (pr_mono (by have := hlow x hx; omega)).trans (hcount x hx))

end Precarious
