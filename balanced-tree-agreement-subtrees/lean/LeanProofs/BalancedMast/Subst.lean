import LeanProofs.BalancedMast.Basic

/-!
# The substitution lemma (Lemma 3.1 of the note)

`S.bind A` is `S°[A]`: every leaf `z` of `S` becomes the root of `A z`. If the label sets of the
`A z` are pairwise disjoint, then each `(A z).L` is a cluster of `S.bind A`, triples inside one
block are those of `A z`, and triples across three blocks are those of `S` on the block names.
-/

namespace BalancedMast
namespace Tree

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

/-- Substitution: replace each leaf `z` by the tree `A z`. -/
def bind : Tree α → (α → Tree β) → Tree β
  | leaf z, A => A z
  | node l r, A => node (bind l A) (bind r A)

/-- Relabelling, as substitution of single leaves. -/
def map (f : α → β) (S : Tree α) : Tree β := S.bind fun z => leaf (f z)

lemma mem_L_bind {S : Tree α} {A : α → Tree β} {x : β} :
    x ∈ (S.bind A).L ↔ ∃ z ∈ S.L, x ∈ (A z).L := by
  induction S with
  | leaf z => simp [bind]
  | node l r ihl ihr =>
    simp only [bind, L_node, Finset.mem_union, ihl, ihr]
    constructor
    · rintro (⟨z, hz, hx⟩ | ⟨z, hz, hx⟩)
      · exact ⟨z, Or.inl hz, hx⟩
      · exact ⟨z, Or.inr hz, hx⟩
    · rintro ⟨z, hz | hz, hx⟩
      · exact Or.inl ⟨z, hz, hx⟩
      · exact Or.inr ⟨z, hz, hx⟩

/-- The blocks `(A z).L`, `z ∈ S.L`, are pairwise disjoint. -/
def BlocksDisjoint (S : Tree α) (A : α → Tree β) : Prop :=
  ∀ z ∈ S.L, ∀ z' ∈ S.L, z ≠ z' → Disjoint (A z).L (A z').L

lemma BlocksDisjoint.eq {S : Tree α} {A : α → Tree β} (hd : S.BlocksDisjoint A) {z z' : α}
    (hz : z ∈ S.L) (hz' : z' ∈ S.L) {x : β} (hx : x ∈ (A z).L) (hx' : x ∈ (A z').L) :
    z = z' := by
  by_contra h; exact Finset.disjoint_left.1 (hd z hz z' hz' h) hx hx'

lemma BlocksDisjoint.mono {S S' : Tree α} {A : α → Tree β} (hd : S.BlocksDisjoint A)
    (h : S'.L ⊆ S.L) : S'.BlocksDisjoint A :=
  fun z hz z' hz' hne => hd z (h hz) z' (h hz') hne

lemma phylo_bind {S : Tree α} {A : α → Tree β} (hS : S.Phylo) (hA : ∀ z ∈ S.L, (A z).Phylo)
    (hd : S.BlocksDisjoint A) : (S.bind A).Phylo := by
  induction S with
  | leaf z => exact hA z (by simp)
  | node l r ihl ihr =>
    obtain ⟨hl, hr, hlr⟩ := phylo_node.1 hS
    refine phylo_node.2 ⟨ihl hl (fun z hz => hA z (by simp [hz])) (hd.mono (by simp)),
      ihr hr (fun z hz => hA z (by simp [hz])) (hd.mono (by simp)), ?_⟩
    refine Finset.disjoint_left.2 fun x hx hx' => ?_
    obtain ⟨z, hz, hxz⟩ := mem_L_bind.1 hx
    obtain ⟨z', hz', hxz'⟩ := mem_L_bind.1 hx'
    have := hd.eq (by simp [hz]) (by simp [hz']) hxz hxz'
    subst this
    exact Finset.disjoint_left.1 hlr hz hz'

lemma mem_subtrees_bind {S : Tree α} {A : α → Tree β} {s : Tree β}
    (hs : s ∈ (S.bind A).subtrees) :
    (∃ s₀ ∈ S.subtrees, s = s₀.bind A) ∨ (∃ z ∈ S.L, s ∈ (A z).subtrees) := by
  induction S with
  | leaf z => exact Or.inr ⟨z, by simp, hs⟩
  | node l r ihl ihr =>
    simp only [bind, subtrees, List.mem_cons, List.mem_append] at hs
    rcases hs with rfl | hs | hs
    · exact Or.inl ⟨node l r, self_mem_subtrees _, rfl⟩
    · rcases ihl hs with ⟨s₀, h₀, rfl⟩ | ⟨z, hz, h⟩
      · exact Or.inl ⟨s₀, by simp [subtrees, h₀], rfl⟩
      · exact Or.inr ⟨z, by simp [hz], h⟩
    · rcases ihr hs with ⟨s₀, h₀, rfl⟩ | ⟨z, hz, h⟩
      · exact Or.inl ⟨s₀, by simp [subtrees, h₀], rfl⟩
      · exact Or.inr ⟨z, by simp [hz], h⟩

lemma bind_mem_subtrees {S s₀ : Tree α} {A : α → Tree β} (h : s₀ ∈ S.subtrees) :
    s₀.bind A ∈ (S.bind A).subtrees := by
  induction S with
  | leaf z => simp [subtrees] at h; subst h; exact self_mem_subtrees _
  | node l r ihl ihr =>
    simp only [subtrees, List.mem_cons, List.mem_append] at h
    rcases h with rfl | h | h
    · exact self_mem_subtrees _
    · simp [bind, subtrees, ihl h]
    · simp [bind, subtrees, ihr h]

lemma block_mem_subtrees {S : Tree α} {A : α → Tree β} {z : α} {s : Tree β} (hz : z ∈ S.L)
    (h : s ∈ (A z).subtrees) : s ∈ (S.bind A).subtrees := by
  induction S with
  | leaf z' => simp at hz; subst hz; exact h
  | node l r ihl ihr =>
    simp only [L_node, Finset.mem_union] at hz
    rcases hz with hz | hz
    · simp [bind, subtrees, ihl hz]
    · simp [bind, subtrees, ihr hz]

/-- Triples inside one block are those of the substituted tree. -/
lemma displays_bind_block {S : Tree α} {A : α → Tree β} (hd : S.BlocksDisjoint A) {z : α}
    (hz : z ∈ S.L) {a b c : β} (ha : a ∈ (A z).L) (hc : c ∈ (A z).L) :
    (S.bind A).Displays a b c ↔ (A z).Displays a b c := by
  constructor
  · rintro ⟨s, hs, has, hbs, hcs⟩
    rcases mem_subtrees_bind hs with ⟨s₀, h₀, rfl⟩ | ⟨z', hz', hs'⟩
    · obtain ⟨z', hz', haz'⟩ := mem_L_bind.1 has
      have := hd.eq hz (L_subset_of_mem_subtrees h₀ hz') ha haz'
      subst this
      exact absurd (mem_L_bind.2 ⟨z, hz', hc⟩) hcs
    · have := hd.eq hz hz' ha (L_subset_of_mem_subtrees hs' has)
      subst this
      exact ⟨s, hs', has, hbs, hcs⟩
  · rintro ⟨s, hs, has, hbs, hcs⟩
    exact ⟨s, block_mem_subtrees hz hs, has, hbs, hcs⟩

/-- Triples across three blocks are those of the skeleton on the block names. -/
lemma displays_bind_skeleton {S : Tree α} {A : α → Tree β} (hd : S.BlocksDisjoint A)
    {z₁ z₂ z₃ : α} (h₁ : z₁ ∈ S.L) (h₂ : z₂ ∈ S.L) (h₃ : z₃ ∈ S.L) (h₁₂ : z₁ ≠ z₂)
    {a b c : β} (ha : a ∈ (A z₁).L) (hb : b ∈ (A z₂).L) (hc : c ∈ (A z₃).L) :
    (S.bind A).Displays a b c ↔ S.Displays z₁ z₂ z₃ := by
  constructor
  · rintro ⟨s, hs, has, hbs, hcs⟩
    rcases mem_subtrees_bind hs with ⟨s₀, h₀, rfl⟩ | ⟨z', hz', hs'⟩
    · obtain ⟨y₁, hy₁, ha'⟩ := mem_L_bind.1 has
      obtain ⟨y₂, hy₂, hb'⟩ := mem_L_bind.1 hbs
      have e₁ := hd.eq h₁ (L_subset_of_mem_subtrees h₀ hy₁) ha ha'
      have e₂ := hd.eq h₂ (L_subset_of_mem_subtrees h₀ hy₂) hb hb'
      subst e₁; subst e₂
      exact ⟨s₀, h₀, hy₁, hy₂, fun h => hcs (mem_L_bind.2 ⟨z₃, h, hc⟩)⟩
    · have e₁ := hd.eq h₁ hz' ha (L_subset_of_mem_subtrees hs' has)
      have e₂ := hd.eq h₂ hz' hb (L_subset_of_mem_subtrees hs' hbs)
      exact absurd (e₁.trans e₂.symm) h₁₂
  · rintro ⟨s₀, h₀, hz₁, hz₂, hz₃⟩
    refine ⟨s₀.bind A, bind_mem_subtrees h₀, mem_L_bind.2 ⟨z₁, hz₁, ha⟩,
      mem_L_bind.2 ⟨z₂, hz₂, hb⟩, fun h => ?_⟩
    obtain ⟨y, hy, hc'⟩ := mem_L_bind.1 h
    have := hd.eq h₃ (L_subset_of_mem_subtrees h₀ hy) hc hc'
    subst this
    exact hz₃ hy

/-- **Substitution lemma.** `mast(S°[A], T°[B]) ≤ mast(S°, T°) · max_z mast(A_z, B_z)`. -/
theorem mast_bind_le {S T : Tree α} {A B : α → Tree β} (hL : S.L = T.L)
    (hdA : S.BlocksDisjoint A) (hAB : ∀ z ∈ S.L, (A z).L = (B z).L) {K : ℕ}
    (hK : ∀ z ∈ S.L, mast (A z) (B z) ≤ K) :
    mast (S.bind A) (T.bind B) ≤ mast S T * K := by
  have hdB : T.BlocksDisjoint B := by
    intro z hz z' hz' hne
    rw [← hL] at hz hz'
    rw [← hAB z hz, ← hAB z' hz']
    exact hdA z hz z' hz' hne
  refine mast_le fun Y hY => ?_
  have hYS : ∀ x ∈ Y, x ∈ (S.bind A).L := fun x hx => (Finset.mem_inter.1 (hY.1 hx)).1
  let ZY := S.L.filter fun z => (Y ∩ (A z).L).Nonempty
  -- `Y` is the disjoint union of its blocks
  have hcard : Y.card = ∑ z ∈ ZY, (Y ∩ (A z).L).card := by
    rw [← Finset.card_biUnion]
    · congr 1
      ext x
      simp only [Finset.mem_biUnion, Finset.mem_inter, ZY, Finset.mem_filter]
      constructor
      · intro hx
        obtain ⟨z, hz, hxz⟩ := mem_L_bind.1 (hYS x hx)
        exact ⟨z, ⟨hz, x, Finset.mem_inter.2 ⟨hx, hxz⟩⟩, hx, hxz⟩
      · rintro ⟨_, _, hx, _⟩; exact hx
    · intro z hz z' hz' hne
      refine Finset.disjoint_left.2 fun x hx hx' => ?_
      exact Finset.disjoint_left.1
        (hdA z (Finset.mem_filter.1 hz).1 z' (Finset.mem_filter.1 hz').1 hne)
        (Finset.mem_inter.1 hx).2 (Finset.mem_inter.1 hx').2
  -- each block is an agreement set of `A z` and `B z`
  have hblock : ∀ z ∈ ZY, (Y ∩ (A z).L).card ≤ K := by
    intro z hz
    have hzS := (Finset.mem_filter.1 hz).1
    have hzT : z ∈ T.L := hL ▸ hzS
    refine (le_mast (S := A z) (T := B z) ⟨?_, fun a ha b hb c hc => ?_⟩).trans (hK z hzS)
    · intro x hx
      have := (Finset.mem_inter.1 hx).2
      exact Finset.mem_inter.2 ⟨this, hAB z hzS ▸ this⟩
    · have ha := (Finset.mem_inter.1 ha).2
      have hc := (Finset.mem_inter.1 hc).2
      rw [← displays_bind_block hdA hzS ha hc,
        ← displays_bind_block hdB hzT (hAB z hzS ▸ ha) (hAB z hzS ▸ hc)]
      exact hY.2 a (Finset.mem_inter.1 ‹a ∈ Y ∩ _›).1 b (Finset.mem_inter.1 hb).1 c
        (Finset.mem_inter.1 ‹c ∈ Y ∩ _›).1
  -- the occupied blocks form an agreement set of the skeletons
  have hskel : ZY.card ≤ mast S T := by
    refine le_mast ⟨fun z hz => ?_, fun z₁ h₁ z₂ h₂ z₃ h₃ => ?_⟩
    · have := (Finset.mem_filter.1 hz).1
      exact Finset.mem_inter.2 ⟨this, hL ▸ this⟩
    have m : ∀ z ∈ ZY, z ∈ S.L ∧ z ∈ T.L := fun z hz =>
      ⟨(Finset.mem_filter.1 hz).1, hL ▸ (Finset.mem_filter.1 hz).1⟩
    by_cases hdist : z₁ ≠ z₂ ∧ z₁ ≠ z₃ ∧ z₂ ≠ z₃
    · obtain ⟨a, ha⟩ := (Finset.mem_filter.1 h₁).2
      obtain ⟨b, hb⟩ := (Finset.mem_filter.1 h₂).2
      obtain ⟨c, hc⟩ := (Finset.mem_filter.1 h₃).2
      obtain ⟨haY, haA⟩ := Finset.mem_inter.1 ha
      obtain ⟨hbY, hbA⟩ := Finset.mem_inter.1 hb
      obtain ⟨hcY, hcA⟩ := Finset.mem_inter.1 hc
      rw [← displays_bind_skeleton hdA (m _ h₁).1 (m _ h₂).1 (m _ h₃).1 hdist.1 haA hbA hcA,
        ← displays_bind_skeleton hdB (m _ h₁).2 (m _ h₂).2 (m _ h₃).2 hdist.1
          (hAB z₁ (m _ h₁).1 ▸ haA) (hAB z₂ (m _ h₂).1 ▸ hbA) (hAB z₃ (m _ h₃).1 ▸ hcA)]
      exact hY.2 a haY b hbY c hcY
    · rw [displays_iff_of_not_distinct (m _ h₁).1 (m _ h₂).1 (m _ h₃).1 hdist,
        displays_iff_of_not_distinct (m _ h₁).2 (m _ h₂).2 (m _ h₃).2 hdist]
  calc Y.card = ∑ z ∈ ZY, (Y ∩ (A z).L).card := hcard
    _ ≤ ZY.card • K := Finset.sum_le_card_nsmul _ _ _ hblock
    _ = ZY.card * K := smul_eq_mul _ _
    _ ≤ mast S T * K := Nat.mul_le_mul_right _ hskel

end Tree
end BalancedMast
