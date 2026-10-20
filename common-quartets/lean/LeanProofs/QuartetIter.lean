import Mathlib

/-!
Exponential upper bound for the common-quartet number h(k) (Snir-Yuster's question, arXiv 2602.23096 §5):
any k ≥ 2 binary trees on n ≥ 2·3^(k-1) + 1 common leaves share a quartet split.

A tree is abstracted as a split system on its leaf set: `Sep X Y` says some edge has X on one side and Y on the
other. The two cited facts about binary trees are the axioms: separation passes to subsets and is symmetric, and
(the 1/3-2/3 lemma, applied to the tree restricted to U) every leaf set U with |U| ≥ 2 has a separated split C | U \ C
with both sides ≥ |U|/3. A quartet ab|cd is displayed iff `Sep {a,b} {c,d}`, so the conclusion (X, Y of size ≥ 2,
separated in every tree) gives a common quartet.

Proved here: Spencer's cell lemma and the iteration.
-/

namespace QuartetIter

open Finset

variable {α : Type*} [DecidableEq α]

structure SplitSys (α : Type*) [DecidableEq α] where
  Sep : Finset α → Finset α → Prop
  mono : ∀ {X Y X' Y'}, Sep X Y → X' ⊆ X → Y' ⊆ Y → Sep X' Y'
  symm : ∀ {X Y}, Sep X Y → Sep Y X
  third : ∀ U : Finset α, 2 ≤ U.card →
    ∃ C ⊆ U, Sep C (U \ C) ∧ U.card ≤ 3 * C.card ∧ U.card ≤ 3 * (U \ C).card

/-- Spencer's cell lemma: two bipartitions of U with all four parts ≥ |U|/3 have opposite cells ≥ |U|/6. -/
theorem cell (U X C : Finset α) (hX : X ⊆ U) (hC : C ⊆ U)
    (h1 : U.card ≤ 3 * X.card) (h2 : U.card ≤ 3 * (U \ X).card)
    (h3 : U.card ≤ 3 * C.card) (h4 : U.card ≤ 3 * (U \ C).card) :
    (U.card ≤ 6 * (X ∩ C).card ∧ U.card ≤ 6 * ((U \ X) \ C).card) ∨
    (U.card ≤ 6 * (X \ C).card ∧ U.card ≤ 6 * ((U \ X) ∩ C).card) := by
  have e1 := card_inter_add_card_sdiff X C
  have e2 := card_inter_add_card_sdiff (U \ X) C
  have e3 : (X ∩ C).card + ((U \ X) ∩ C).card = C.card := by
    rw [← card_union_of_disjoint]
    · congr 1; ext a; simp only [mem_union, mem_inter, mem_sdiff]; constructor
      · rintro (⟨-, h⟩ | ⟨-, h⟩) <;> exact h
      · intro h; by_cases hx : a ∈ X
        · exact Or.inl ⟨hx, h⟩
        · exact Or.inr ⟨⟨hC h, hx⟩, h⟩
    · rw [disjoint_left]; intro a h h'; simp only [mem_inter, mem_sdiff] at h h'; exact h'.1.2 h.1
  have e4 : (X \ C).card + ((U \ X) \ C).card = (U \ C).card := by
    rw [← card_union_of_disjoint]
    · congr 1; ext a; simp only [mem_union, mem_sdiff]; constructor
      · rintro (⟨h, h'⟩ | ⟨⟨h, -⟩, h'⟩) <;> [exact ⟨hX h, h'⟩; exact ⟨h, h'⟩]
      · rintro ⟨h, h'⟩; by_cases hx : a ∈ X
        · exact Or.inl ⟨hx, h'⟩
        · exact Or.inr ⟨⟨h, hx⟩, h'⟩
    · rw [disjoint_left]; intro a h h'; simp only [mem_sdiff] at h h'; exact h'.1.2 h.1
  omega

/-- One step: X, Y separated in all earlier trees, U = X ∪ Y with both parts ≥ |U|/3; a new tree T yields
X' ⊆ X, Y' ⊆ Y separated in T with 6|X'|, 6|Y'| ≥ |U|. -/
theorem step (T : SplitSys α) (X Y : Finset α) (hd : Disjoint X Y) (h2 : 2 ≤ (X ∪ Y).card)
    (hXc : (X ∪ Y).card ≤ 3 * X.card) (hYc : (X ∪ Y).card ≤ 3 * Y.card) :
    ∃ X' ⊆ X, ∃ Y' ⊆ Y, T.Sep X' Y' ∧ (X ∪ Y).card ≤ 6 * X'.card ∧ (X ∪ Y).card ≤ 6 * Y'.card := by
  obtain ⟨C, hCU, hsep, h3, h4⟩ := T.third (X ∪ Y) h2
  have hUX : (X ∪ Y) \ X = Y := by
    ext a; simp only [mem_sdiff, mem_union]; constructor
    · rintro ⟨h | h, h'⟩; exacts [absurd h h', h]
    · intro h; exact ⟨Or.inr h, disjoint_right.mp hd h⟩
  have hc := cell (X ∪ Y) X C subset_union_left hCU hXc (by rw [hUX]; exact hYc) h3 h4
  rw [hUX] at hc
  rcases hc with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · refine ⟨X ∩ C, inter_subset_left, Y \ C, sdiff_subset, ?_, ha, hb⟩
    refine T.mono hsep inter_subset_right ?_
    intro a h; simp only [mem_sdiff, mem_union] at h ⊢; exact ⟨Or.inr h.1, h.2⟩
  · refine ⟨X \ C, sdiff_subset, Y ∩ C, inter_subset_left, ?_, ha, hb⟩
    refine T.symm (T.mono hsep inter_subset_right ?_)
    intro a h; simp only [mem_sdiff, mem_union] at h ⊢; exact ⟨Or.inl h.1, h.2⟩

/-- After j ≥ 2 trees: X, Y separated in all of them with 2·3^(j-1)·|X|, 2·3^(j-1)·|Y| ≥ n. -/
theorem iterate (U : Finset α) (T : ℕ → SplitSys α) (hU : 2 ≤ U.card) :
    ∀ j, 2 ≤ j → ∃ X ⊆ U, ∃ Y ⊆ U, Disjoint X Y ∧ (∀ i < j, (T i).Sep X Y) ∧
      U.card ≤ 2 * 3 ^ (j - 1) * X.card ∧ U.card ≤ 2 * 3 ^ (j - 1) * Y.card := by
  intro j hj
  induction j, hj using Nat.le_induction with
  | base =>
    obtain ⟨C, hCU, hsep, h3, h4⟩ := (T 0).third U hU
    have hu : C ∪ (U \ C) = U := union_sdiff_of_subset hCU
    have hd : Disjoint C (U \ C) := disjoint_sdiff
    obtain ⟨X, hX, Y, hY, hs, hx, hy⟩ := step (T 1) C (U \ C) hd (by rw [hu]; exact hU)
      (by rw [hu]; exact h3) (by rw [hu]; exact h4)
    rw [hu] at hx hy
    refine ⟨X, hX.trans hCU, Y, hY.trans sdiff_subset, disjoint_of_subset_left hX
      (disjoint_of_subset_right hY hd), ?_, by simpa using hx, by simpa using hy⟩
    intro i hi
    interval_cases i
    · exact (T 0).mono hsep hX hY
    · exact hs
  | succ j hj ih =>
    obtain ⟨X, hXU, Y, hYU, hd, hs, hx, hy⟩ := ih
    -- trim to a common size m = min |X| |Y|
    set m := min X.card Y.card with hm
    obtain ⟨X0, hX0, hX0c⟩ := exists_subset_card_eq (show m ≤ X.card from min_le_left _ _)
    obtain ⟨Y0, hY0, hY0c⟩ := exists_subset_card_eq (show m ≤ Y.card from min_le_right _ _)
    have hd0 : Disjoint X0 Y0 := disjoint_of_subset_left hX0 (disjoint_of_subset_right hY0 hd)
    have hc0 : (X0 ∪ Y0).card = 2 * m := by rw [card_union_of_disjoint hd0]; omega
    have hpow : 0 < 3 ^ (j - 1) := by positivity
    have hm1 : U.card ≤ 2 * 3 ^ (j - 1) * m := by
      rcases min_choice X.card Y.card with h | h <;> rw [hm, h] <;> assumption
    have hm2 : 1 ≤ m := by
      by_contra h; push Not at h; interval_cases m; omega
    obtain ⟨X', hX', Y', hY', hs', hx', hy'⟩ :=
      step (T j) X0 Y0 hd0 (by omega) (by omega) (by omega)
    refine ⟨X', (hX'.trans hX0).trans hXU, Y', (hY'.trans hY0).trans hYU,
      disjoint_of_subset_left hX' (disjoint_of_subset_right hY' hd0), ?_, ?_, ?_⟩
    · intro i hi
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h | h
      · exact (T i).mono (hs i h) (hX'.trans hX0) (hY'.trans hY0)
      · subst h; exact hs'
    · have : j + 1 - 1 = (j - 1) + 1 := by omega
      rw [this, pow_succ]; rw [hc0] at hx'; nlinarith
    · have : j + 1 - 1 = (j - 1) + 1 := by omega
      rw [this, pow_succ]; rw [hc0] at hy'; nlinarith

/-- k ≥ 2 trees on n ≥ 2·3^(k-1) + 1 leaves: separated X, Y with at least two leaves each, hence a common
quartet (a, b ∈ X, c, d ∈ Y). So h(k) ≤ 2·3^(k-1) + 1. -/
theorem common_quartet (U : Finset α) (k : ℕ) (hk : 2 ≤ k) (T : ℕ → SplitSys α)
    (hn : 2 * 3 ^ (k - 1) + 1 ≤ U.card) :
    ∃ X ⊆ U, ∃ Y ⊆ U, Disjoint X Y ∧ 2 ≤ X.card ∧ 2 ≤ Y.card ∧ ∀ i < k, (T i).Sep X Y := by
  have hpow : 0 < 3 ^ (k - 1) := by positivity
  obtain ⟨X, hX, Y, hY, hd, hs, hx, hy⟩ := iterate U T (by omega) k hk
  refine ⟨X, hX, Y, hY, hd, ?_, ?_, hs⟩
  · by_contra h; push Not at h; interval_cases h' : X.card <;> nlinarith
  · by_contra h; push Not at h; interval_cases h' : Y.card <;> nlinarith

end QuartetIter
