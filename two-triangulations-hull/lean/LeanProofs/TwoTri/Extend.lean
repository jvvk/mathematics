import LeanProofs.TwoTri.EdgeCount
import LeanProofs.TwoTri.Nine

/-!
# Extending non-crossing sets; the edge-count criterion for a triangulation

* every non-crossing set of segments extends to a triangulation;
* a non-crossing set with `3n - 3 - h` segments is a triangulation (the argument of Section 3);
* `|segs P| = C(n, 2)`.
-/

set_option linter.unusedSectionVars false

namespace TwoTri

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

instance (T : Finset (Sym2 (K × K))) : Decidable (NonCross T) := by unfold NonCross; infer_instance

lemma not_cross_self (s : Sym2 (K × K)) : ¬ Cross s s := by
  induction s using Sym2.ind with
  | _ a b => rw [cross_mk]; intro h; have := h.1; simp at this

/-- Every non-crossing set of segments extends to a triangulation. -/
theorem extend {P : Finset (K × K)} {S : Finset (Sym2 (K × K))} (hS : S ⊆ segs P)
    (hnc : NonCross S) : ∃ T, S ⊆ T ∧ IsTri P T := by
  classical
  induction h : (segs P \ S).card generalizing S with
  | zero =>
    refine ⟨S, subset_rfl, hS, hnc, fun s hs hsS => ?_⟩
    have : s ∈ segs P \ S := Finset.mem_sdiff.mpr ⟨hs, hsS⟩
    rw [Finset.card_eq_zero] at h; rw [h] at this; simp at this
  | succ m ih =>
    by_cases hmax : ∀ s ∈ segs P, s ∉ S → ∃ t ∈ S, Cross s t
    · exact ⟨S, subset_rfl, hS, hnc, hmax⟩
    push Not at hmax
    obtain ⟨s, hs, hsS, hfree⟩ := hmax
    have hS' : insert s S ⊆ segs P := Finset.insert_subset hs hS
    have hnc' : NonCross (insert s S) := by
      intro a ha b hb
      rcases Finset.mem_insert.mp ha with h1 | h1 <;> rcases Finset.mem_insert.mp hb with h2 | h2
      · rw [h1, h2]; exact not_cross_self _
      · rw [h1]; exact hfree b h2
      · rw [h2]; exact fun h => hfree a h1 (cross_comm.mp h)
      · exact hnc a h1 b h2
    have hcard : (segs P \ insert s S).card = m := by
      have : segs P \ insert s S = (segs P \ S).erase s := by
        ext x; simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_erase]; tauto
      rw [this, Finset.card_erase_of_mem (Finset.mem_sdiff.mpr ⟨hs, hsS⟩), h]; rfl
    obtain ⟨T, hST, hT⟩ := ih hS' hnc' hcard
    exact ⟨T, (Finset.subset_insert s S).trans hST, hT⟩

/-- **Section 3, the edge-count criterion.** A non-crossing set of `3n - 3 - h` segments of
`n ≥ 3` points in general position is a triangulation. -/
theorem isTri_of_card {P : Finset (K × K)} (hP : GenPos P) (h3 : 3 ≤ P.card)
    {S : Finset (Sym2 (K × K))} (hS : S ⊆ segs P) (hnc : NonCross S)
    (hcard : S.card + 3 + (hullEdges P).card = 3 * P.card) : IsTri P S := by
  obtain ⟨T, hST, hT⟩ := extend hS hnc
  have := edge_count hP h3 hT
  have hEq : S = T := Finset.eq_of_subset_of_card_le hST (by omega)
  rw [hEq]; exact hT

lemma card_segs (P : Finset (K × K)) : (segs P).card = P.card.choose 2 := by
  classical
  have hdiag : (P.sym2.filter (fun s => s.IsDiag)).card = P.card := by
    rw [show P.sym2.filter (fun s => s.IsDiag) = P.image (fun a => s(a, a)) from ?_]
    · exact Finset.card_image_of_injective _ (fun a b h => by simpa using h)
    · ext s
      induction s using Sym2.ind with
      | _ a b =>
      simp only [Finset.mem_filter, Finset.mk_mem_sym2_iff, Sym2.mk_isDiag_iff,
        Finset.mem_image, Sym2.eq_iff]
      constructor
      · rintro ⟨⟨ha, -⟩, rfl⟩; exact ⟨a, ha, Or.inl ⟨rfl, rfl⟩⟩
      · rintro ⟨c, hc, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ <;> exact ⟨⟨hc, hc⟩, rfl⟩
  have h := Finset.card_filter_add_card_filter_not (s := P.sym2) (p := fun s => s.IsDiag)
  rw [hdiag, Finset.card_sym2, Nat.choose_succ_succ, Nat.choose_one_right] at h
  unfold segs; simp only [Nat.reduceSucc] at h ⊢; omega

/-- The nine-point example: `A` and `B` are non-crossing with `19 = 3·9 - 3 - 5` edges each,
hence triangulations (the paper's argument, not the direct maximality check). -/
theorem nine_by_count : IsTri Nine.P9 Nine.A9 ∧ IsTri Nine.P9 Nine.B9 := by
  have hh : (hullEdges Nine.P9).card = 5 := by rw [Nine.hull_P9]; exact Nine.card_H9
  constructor
  · exact isTri_of_card Nine.genPos_P9 (by rw [Nine.card_P9]; norm_num) (by decide +kernel)
      (by decide +kernel) (by rw [hh, Nine.card_P9]; decide +kernel)
  · exact isTri_of_card Nine.genPos_P9 (by rw [Nine.card_P9]; norm_num) (by decide +kernel)
      (by decide +kernel) (by rw [hh, Nine.card_P9]; decide +kernel)

end TwoTri
