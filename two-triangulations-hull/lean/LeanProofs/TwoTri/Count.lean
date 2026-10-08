import Mathlib.Tactic

/-!
# Two counting lemmas
-/

namespace TwoTri

/-- Pairs of consecutive elements of a finite linearly ordered set. -/
def consecPairs {K : Type*} [LinearOrder K] (S : Finset K) : Finset (K × K) :=
  (S ×ˢ S).filter (fun ab => ab.1 < ab.2 ∧ ∀ c ∈ S, ¬ (ab.1 < c ∧ c < ab.2))

/-- A nonempty finite linear order has one fewer consecutive pair than elements. -/
theorem card_consecPairs {K : Type*} [LinearOrder K] (S : Finset K) (hS : S.Nonempty) :
    (consecPairs S).card + 1 = S.card := by
  classical
  induction S using Finset.induction_on_max with
  | empty => simp at hS
  | insert m s hlt ih =>
    have hm : m ∉ s := fun h => lt_irrefl _ (hlt m h)
    rcases s.eq_empty_or_nonempty with rfl | hs
    · simp [consecPairs]
    · set M := s.max' hs
      have hM : M ∈ s := s.max'_mem hs
      have key : consecPairs (insert m s) = insert (M, m) (consecPairs s) := by
        ext ⟨a, b⟩
        simp only [consecPairs, Finset.mem_filter, Finset.mem_product, Finset.mem_insert,
          Prod.mk.injEq]
        constructor
        · rintro ⟨⟨ha, hb⟩, hab, hno⟩
          rcases hb with rfl | hb
          · rcases ha with rfl | ha
            · exact absurd hab (lt_irrefl _)
            · left
              refine ⟨le_antisymm (s.le_max' a ha) ?_, rfl⟩
              by_contra hc; push Not at hc
              exact hno M (Or.inr hM) ⟨hc, hlt M hM⟩
          · rcases ha with rfl | ha
            · exact absurd (hlt b hb) (not_lt.mpr hab.le)
            · right
              exact ⟨⟨ha, hb⟩, hab, fun c hc => hno c (Or.inr hc)⟩
        · rintro (⟨rfl, rfl⟩ | ⟨⟨ha, hb⟩, hab, hno⟩)
          · refine ⟨⟨Or.inr hM, Or.inl rfl⟩, hlt _ hM, ?_⟩
            rintro c (rfl | hc) ⟨h1, h2⟩
            · exact lt_irrefl _ h2
            · exact absurd (s.le_max' c hc) (not_le.mpr h1)
          · refine ⟨⟨Or.inr ha, Or.inr hb⟩, hab, ?_⟩
            rintro c (rfl | hc) ⟨h1, h2⟩
            · exact absurd (hlt b hb) (not_lt.mpr h2.le)
            · exact hno c hc ⟨h1, h2⟩
      have hnot : (M, m) ∉ consecPairs s := by
        intro h
        simp only [consecPairs, Finset.mem_filter, Finset.mem_product] at h
        exact hm h.1.2
      rw [key, Finset.card_insert_of_notMem hnot, Finset.card_insert_of_notMem hm, ← ih hs]

end TwoTri
