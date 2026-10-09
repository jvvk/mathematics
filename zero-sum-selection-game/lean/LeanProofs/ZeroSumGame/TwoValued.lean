import LeanProofs.ZeroSumGame.Dimension

/-!
# Rows with two values: a universal–existential normal form

Every entry of row `i` is `val i true` or `val i false` (distinct). Write `cnt i b` for the number
of positions carrying `val i b`. The Enemy, selecting `k i` positions, can isolate value `b`
exactly when `k i ≤ cnt i b`; when neither value can be isolated, every selection offers both. The
matrix is winning exactly when, for every legal way `E` of isolating values (`E i = some b`:
isolate `b`; `E i = none`: allowed only when nothing can be isolated), You can choose one value
per row, respecting the isolated ones, with sum zero. With universal rows (both isolable), fixed
rows (one isolable) and existential rows (none isolable) this is a `∀∃` subset-sum statement,
which is how hardness is proved.
-/

open Finset

namespace ZeroSumGame

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- Positions of row `i` carrying `val i b`. -/
noncomputable def posOf {N : I → ℕ} (a : Array N) (val : I → Bool → ℝ) (i : I) (b : Bool) :
    Finset (Fin (N i)) :=
  univ.filter fun j => a ⟨i, j⟩ = val i b

omit [DecidableEq I] in
/-- **Two-valued normal form.** -/
theorem two_valued {N : I → ℕ} (k : I → ℕ) (hk : ∀ i, k i ≤ N i) (hk1 : ∀ i, 1 ≤ k i) (a : Array N)
    (val : I → Bool → ℝ) (hval : ∀ i, val i true ≠ val i false)
    (htwo : ∀ i j, a ⟨i, j⟩ = val i true ∨ a ⟨i, j⟩ = val i false) :
    Winning k a ↔
      ∀ E : I → Option Bool, (∀ i b, E i = some b → k i ≤ (posOf a val i b).card) →
        (∀ i, E i = none → (posOf a val i true).card < k i ∧ (posOf a val i false).card < k i) →
        ∃ c : I → Bool, (∀ i b, E i = some b → c i = b) ∧ ∑ i, val i (c i) = 0 := by
  classical
  constructor
  · intro hw E hiso hnone
    -- the Enemy's selection realising E
    have hsel : ∀ i, ∃ S : Finset (Fin (N i)), S.card = k i ∧
        (∀ b, E i = some b → S ⊆ posOf a val i b) := by
      intro i
      cases h : E i with
      | none =>
        obtain ⟨S, -, hS⟩ := exists_subset_card_eq (s := (univ : Finset (Fin (N i))))
          (by simpa using hk i)
        exact ⟨S, hS, fun b hb => by simp at hb⟩
      | some b =>
        obtain ⟨S, hsub, hS⟩ := exists_subset_card_eq (hiso i b h)
        exact ⟨S, hS, fun b' hb' => by
          simp only [Option.some.injEq] at hb'; subst hb'; exact hsub⟩
    choose S hScard hSsub using hsel
    obtain ⟨t, ht, hz⟩ := hw S hScard
    -- read off the chosen values
    refine ⟨fun i => decide (a ⟨i, t i⟩ = val i true), ?_, ?_⟩
    · intro i b hb
      have hm : t i ∈ posOf a val i b := hSsub i b hb (ht i)
      simp only [posOf, mem_filter, mem_univ, true_and] at hm
      cases b
      · simp [hm, (hval i).symm]
      · simp [hm]
    · rw [← hz]
      unfold transversalSum
      refine Finset.sum_congr rfl fun i _ => ?_
      by_cases h : a ⟨i, t i⟩ = val i true
      · simp [h]
      · have h' : a ⟨i, t i⟩ = val i false := (htwo i (t i)).resolve_left h
        simp [h', Ne.symm (hval i)]
  · intro h S hS
    -- the isolation pattern the Enemy's selection allows
    let E : I → Option Bool := fun i =>
      if (S i ∩ posOf a val i true).Nonempty ∧ k i ≤ (posOf a val i true).card then some true
      else if (S i ∩ posOf a val i false).Nonempty ∧ k i ≤ (posOf a val i false).card
        then some false else none
    have hiso : ∀ i b, E i = some b → k i ≤ (posOf a val i b).card := by
      intro i b hb
      simp only [E] at hb
      split_ifs at hb with h1 h2 <;> simp only [Option.some.injEq] at hb <;> subst hb
      · exact h1.2
      · exact h2.2
    -- if a value cannot be isolated, the selection contains it
    have hmeets : ∀ i b, (posOf a val i b).card < k i → (S i ∩ posOf a val i (!b)).Nonempty := by
      intro i b hlt
      by_contra hne
      rw [not_nonempty_iff_eq_empty] at hne
      have hsub : S i ⊆ posOf a val i b := by
        intro j hj
        have hj' : j ∉ posOf a val i (!b) := fun hm => by
          have : j ∈ S i ∩ posOf a val i (!b) := mem_inter.mpr ⟨hj, hm⟩
          rw [hne] at this; simp at this
        simp only [posOf, mem_filter, mem_univ, true_and] at hj' ⊢
        cases b
        · exact (htwo i j).resolve_left (by simpa using hj')
        · exact (htwo i j).resolve_right (by simpa using hj')
      have := card_le_card hsub
      rw [hS i] at this
      omega
    have hnone : ∀ i, E i = none →
        (posOf a val i true).card < k i ∧ (posOf a val i false).card < k i := by
      intro i hi
      simp only [E] at hi
      split_ifs at hi with h1 h2
      by_contra hc
      rw [not_and_or, not_lt, not_lt] at hc
      rcases hc with hc | hc
      · -- true is isolable; then S i meets the true positions, unless false is not isolable…
        rcases Nat.lt_or_ge (posOf a val i false).card (k i) with hf | hf
        · exact h1 ⟨by simpa using hmeets i false hf, hc⟩
        · -- both isolable: S i meets one of them
          by_cases hm : (S i ∩ posOf a val i true).Nonempty
          · exact h1 ⟨hm, hc⟩
          · apply h2
            refine ⟨?_, hf⟩
            obtain ⟨j, hj⟩ := card_pos.mp (by rw [hS i]; exact hk1 i : 0 < (S i).card)
            refine ⟨j, mem_inter.mpr ⟨hj, ?_⟩⟩
            simp only [posOf, mem_filter, mem_univ, true_and]
            refine (htwo i j).resolve_left fun e => hm ⟨j, mem_inter.mpr ⟨hj, ?_⟩⟩
            simp [posOf, e]
      · rcases Nat.lt_or_ge (posOf a val i true).card (k i) with ht' | ht'
        · exact h2 ⟨by simpa using hmeets i true ht', hc⟩
        · by_cases hm : (S i ∩ posOf a val i true).Nonempty
          · exact h1 ⟨hm, ht'⟩
          · apply h2
            refine ⟨?_, hc⟩
            obtain ⟨j, hj⟩ := card_pos.mp (by rw [hS i]; exact hk1 i : 0 < (S i).card)
            refine ⟨j, mem_inter.mpr ⟨hj, ?_⟩⟩
            simp only [posOf, mem_filter, mem_univ, true_and]
            refine (htwo i j).resolve_left fun e => hm ⟨j, mem_inter.mpr ⟨hj, ?_⟩⟩
            simp [posOf, e]
    obtain ⟨c, hc, hsum⟩ := h E hiso hnone
    -- every chosen value is present in the selection
    have hpresent : ∀ i, (S i ∩ posOf a val i (c i)).Nonempty := by
      intro i
      cases hEi : E i with
      | some b =>
        rw [hc i b hEi]
        simp only [E] at hEi
        split_ifs at hEi with h1 h2 <;> simp only [Option.some.injEq] at hEi <;> subst hEi
        · exact h1.1
        · exact h2.1
      | none =>
        obtain ⟨ht, hf⟩ := hnone i hEi
        cases hci : c i
        · simpa using hmeets i true ht
        · simpa using hmeets i false hf
    choose t ht using hpresent
    refine ⟨t, fun i => (mem_inter.mp (ht i)).1, ?_⟩
    rw [← hsum]
    unfold transversalSum
    refine Finset.sum_congr rfl fun i _ => ?_
    have := (mem_inter.mp (ht i)).2
    simpa [posOf] using this

end ZeroSumGame
