import Mathlib

/-!
# Agreement subtrees: trees, displayed triples, agreement sets

A rooted binary tree with labelled leaves is `Tree α`. It is phylogenetic (`Phylo`) when its leaf
labels are distinct. A vertex `s` of `S` (an element of `S.subtrees`) has cluster `s.L`.
`S` displays the triple `ab|c` when some cluster contains `a` and `b` but not `c`.

A set `Y` of common labels is an agreement set of `S` and `T` when the two trees display the same
triples on `Y`. For phylogenetic trees this is the same as `S|Y ≅ T|Y`: a rooted binary
phylogenetic tree is determined by its triples, and the triples of `S|Y` are those of `S` on `Y`
(`Restrict.lean` proves this equivalence). `mast S T` is the largest size of an agreement set.
-/

namespace BalancedMast

inductive Tree (α : Type*) where
  | leaf : α → Tree α
  | node : Tree α → Tree α → Tree α
  deriving DecidableEq

namespace Tree

variable {α : Type*} [DecidableEq α]

/-- The leaf labels, left to right. -/
def labels : Tree α → List α
  | leaf a => [a]
  | node l r => labels l ++ labels r

/-- The cluster (label set) of a tree. -/
def L (S : Tree α) : Finset α := S.labels.toFinset

/-- Phylogenetic: the leaf labels are distinct. -/
def Phylo (S : Tree α) : Prop := S.labels.Nodup

/-- The pendant subtrees at all vertices, the tree itself and its leaves included. -/
def subtrees : Tree α → List (Tree α)
  | leaf a => [leaf a]
  | node l r => node l r :: (subtrees l ++ subtrees r)

/-- `S` displays the triple `ab|c`. -/
def Displays (S : Tree α) (a b c : α) : Prop :=
  ∃ s ∈ S.subtrees, a ∈ s.L ∧ b ∈ s.L ∧ c ∉ s.L

instance (S : Tree α) (a b c : α) : Decidable (S.Displays a b c) := by
  unfold Displays; infer_instance

/-- `Y` is an agreement set of `S` and `T`. -/
def Agree (S T : Tree α) (Y : Finset α) : Prop :=
  Y ⊆ S.L ∩ T.L ∧ ∀ a ∈ Y, ∀ b ∈ Y, ∀ c ∈ Y, (S.Displays a b c ↔ T.Displays a b c)

instance (S T : Tree α) (Y : Finset α) : Decidable (Agree S T Y) := by
  unfold Agree; infer_instance

/-- The size of a maximum agreement subtree. -/
def mast (S T : Tree α) : ℕ := ((S.L ∩ T.L).powerset.filter (Agree S T)).sup Finset.card

@[simp] lemma L_leaf (a : α) : (leaf a).L = {a} := by simp [L, labels]

@[simp] lemma L_node (l r : Tree α) : (node l r).L = l.L ∪ r.L := by
  ext x; simp [L, labels]

lemma mem_L {S : Tree α} {x : α} : x ∈ S.L ↔ x ∈ S.labels := by simp [L]

lemma phylo_node {l r : Tree α} :
    (node l r).Phylo ↔ l.Phylo ∧ r.Phylo ∧ Disjoint l.L r.L := by
  simp only [Phylo, labels, List.nodup_append, Finset.disjoint_left, mem_L]
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, h2, fun x hx hx' => h3 x hx x hx' rfl⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, h2, fun x hx y hy hxy => h3 hx (hxy ▸ hy)⟩

omit [DecidableEq α] in
lemma self_mem_subtrees (S : Tree α) : S ∈ S.subtrees := by
  cases S <;> simp [subtrees]

lemma L_subset_of_mem_subtrees {S s : Tree α} (h : s ∈ S.subtrees) : s.L ⊆ S.L := by
  induction S with
  | leaf a => simp [subtrees] at h; subst h; exact le_rfl
  | node l r ihl ihr =>
    simp only [subtrees, List.mem_cons, List.mem_append] at h
    rcases h with rfl | h | h
    · exact le_rfl
    · exact (ihl h).trans (by simp)
    · exact (ihr h).trans (by simp)

lemma leaf_mem_subtrees {S : Tree α} {x : α} (h : x ∈ S.L) : leaf x ∈ S.subtrees := by
  induction S with
  | leaf a => simp at h; subst h; simp [subtrees]
  | node l r ihl ihr =>
    simp only [L_node, Finset.mem_union] at h
    simp only [subtrees, List.mem_cons, List.mem_append]
    rcases h with h | h
    · exact Or.inr (Or.inl (ihl h))
    · exact Or.inr (Or.inr (ihr h))

lemma L_nonempty (S : Tree α) : S.L.Nonempty := by
  induction S with
  | leaf a => simp
  | node l r ihl _ => obtain ⟨x, hx⟩ := ihl; exact ⟨x, by simp [hx]⟩

/-! ## Agreement sets and `mast` -/

lemma le_mast {S T : Tree α} {Y : Finset α} (h : Agree S T Y) : Y.card ≤ mast S T :=
  Finset.le_sup (f := Finset.card) (Finset.mem_filter.2 ⟨Finset.mem_powerset.2 h.1, h⟩)

lemma mast_le {S T : Tree α} {k : ℕ} (h : ∀ Y, Agree S T Y → Y.card ≤ k) : mast S T ≤ k :=
  Finset.sup_le fun Y hY => h Y (Finset.mem_filter.1 hY).2

lemma exists_agree_mast (S T : Tree α) : ∃ Y, Agree S T Y ∧ Y.card = mast S T := by
  obtain ⟨Y, hY, h⟩ := Finset.exists_mem_eq_sup
    ((S.L ∩ T.L).powerset.filter (Agree S T))
    ⟨∅, Finset.mem_filter.2 ⟨Finset.empty_mem_powerset _, by simp [Agree]⟩⟩ Finset.card
  exact ⟨Y, (Finset.mem_filter.1 hY).2, h.symm⟩

-- From here on `mast` is used only through `le_mast`, `mast_le` and `exists_agree_mast`.
attribute [irreducible] mast

lemma Agree.mono {S T : Tree α} {Y Y' : Finset α} (h : Agree S T Y) (hY : Y' ⊆ Y) :
    Agree S T Y' :=
  ⟨hY.trans h.1, fun a ha b hb c hc => h.2 a (hY ha) b (hY hb) c (hY hc)⟩

lemma Agree.symm {S T : Tree α} {Y : Finset α} (h : Agree S T Y) : Agree T S Y :=
  ⟨by rw [Finset.inter_comm]; exact h.1, fun a ha b hb c hc => (h.2 a ha b hb c hc).symm⟩

lemma mast_comm (S T : Tree α) : mast S T = mast T S :=
  le_antisymm (mast_le fun _ h => le_mast h.symm) (mast_le fun _ h => le_mast h.symm)

lemma mast_le_card_inter (S T : Tree α) : mast S T ≤ (S.L ∩ T.L).card :=
  mast_le fun _ h => Finset.card_le_card h.1

/-- When two of `a, b, c` coincide, the triple `ab|c` is displayed exactly when `a = b ≠ c`. -/
lemma displays_iff_of_not_distinct {U : Tree α} {a b c : α} (ha : a ∈ U.L) (hb : b ∈ U.L)
    (hc : c ∈ U.L) (h : ¬(a ≠ b ∧ a ≠ c ∧ b ≠ c)) : U.Displays a b c ↔ (a = b ∧ a ≠ c) := by
  constructor
  · rintro ⟨s, _, has, hbs, hcs⟩
    have hac : a ≠ c := fun e => hcs (e ▸ has)
    have hbc : b ≠ c := fun e => hcs (e ▸ hbs)
    exact ⟨by by_contra hab; exact h ⟨hab, hac, hbc⟩, hac⟩
  · rintro ⟨rfl, hac⟩
    exact ⟨leaf a, leaf_mem_subtrees ha, by simp, by simp, by simpa using hac.symm⟩

/-- Every set of at most two common labels is an agreement set. -/
lemma agree_of_card_le_two {S T : Tree α} {Y : Finset α} (hY : Y ⊆ S.L ∩ T.L)
    (h2 : Y.card ≤ 2) : Agree S T Y := by
  refine ⟨hY, fun a ha b hb c hc => ?_⟩
  have hS : ∀ x ∈ Y, x ∈ S.L := fun x hx => (Finset.mem_inter.1 (hY hx)).1
  have hT : ∀ x ∈ Y, x ∈ T.L := fun x hx => (Finset.mem_inter.1 (hY hx)).2
  have hnd : ¬(a ≠ b ∧ a ≠ c ∧ b ≠ c) := by
    rintro ⟨hab, hac, hbc⟩
    have h3 : ({a, b, c} : Finset α).card = 3 := by
      rw [Finset.card_insert_of_notMem (by simp [hab, hac]), Finset.card_pair hbc]
    have := Finset.card_le_card (show ({a, b, c} : Finset α) ⊆ Y by
      intro x hx; simp at hx; rcases hx with rfl | rfl | rfl <;> assumption)
    omega
  rw [displays_iff_of_not_distinct (hS a ha) (hS b hb) (hS c hc) hnd,
    displays_iff_of_not_distinct (hT a ha) (hT b hb) (hT c hc) hnd]

/-! ## Triples at a root -/

lemma displays_mem {S : Tree α} {a b c : α} (h : S.Displays a b c) : a ∈ S.L ∧ b ∈ S.L := by
  obtain ⟨s, hs, ha, hb, _⟩ := h
  exact ⟨L_subset_of_mem_subtrees hs ha, L_subset_of_mem_subtrees hs hb⟩

/-- The triple `ab|c` at a root `node l r`: either `a, b` lie in one half and `c` lies outside
it, or all three lie in one half and that half displays `ab|c`. -/
lemma displays_node {l r : Tree α} {a b c : α} (hc : c ∈ (node l r).L) :
    (node l r).Displays a b c ↔
      (a ∈ l.L ∧ b ∈ l.L ∧ (c ∈ l.L → l.Displays a b c)) ∨
      (a ∈ r.L ∧ b ∈ r.L ∧ (c ∈ r.L → r.Displays a b c)) := by
  constructor
  · rintro ⟨s, hs, has, hbs, hcs⟩
    simp only [subtrees, List.mem_cons, List.mem_append] at hs
    rcases hs with rfl | hs | hs
    · exact absurd hc hcs
    · exact Or.inl ⟨L_subset_of_mem_subtrees hs has, L_subset_of_mem_subtrees hs hbs,
        fun _ => ⟨s, hs, has, hbs, hcs⟩⟩
    · exact Or.inr ⟨L_subset_of_mem_subtrees hs has, L_subset_of_mem_subtrees hs hbs,
        fun _ => ⟨s, hs, has, hbs, hcs⟩⟩
  · rintro (⟨ha, hb, hcl⟩ | ⟨ha, hb, hcr⟩)
    · by_cases hcl' : c ∈ l.L
      · obtain ⟨s, hs, h1, h2, h3⟩ := hcl hcl'
        exact ⟨s, by simp [subtrees, hs], h1, h2, h3⟩
      · exact ⟨l, by simp [subtrees, self_mem_subtrees], ha, hb, hcl'⟩
    · by_cases hcr' : c ∈ r.L
      · obtain ⟨s, hs, h1, h2, h3⟩ := hcr hcr'
        exact ⟨s, by simp [subtrees, hs], h1, h2, h3⟩
      · exact ⟨r, by simp [subtrees, self_mem_subtrees], ha, hb, hcr'⟩

lemma displays_node_of_left {l r : Tree α} (h : (node l r).Phylo) {a b c : α}
    (ha : a ∈ l.L) (hc : c ∈ l.L) : (node l r).Displays a b c ↔ l.Displays a b c := by
  have hd := Finset.disjoint_left.1 (phylo_node.1 h).2.2
  rw [displays_node (by simp [hc])]
  constructor
  · rintro (⟨_, _, h3⟩ | ⟨ha', _, _⟩)
    · exact h3 hc
    · exact absurd ha' (hd ha)
  · intro hl; exact Or.inl ⟨ha, (displays_mem hl).2, fun _ => hl⟩

lemma displays_node_of_right {l r : Tree α} (h : (node l r).Phylo) {a b c : α}
    (ha : a ∈ r.L) (hc : c ∈ r.L) : (node l r).Displays a b c ↔ r.Displays a b c := by
  have hd := Finset.disjoint_left.1 (phylo_node.1 h).2.2
  rw [displays_node (by simp [hc])]
  constructor
  · rintro (⟨ha', _, _⟩ | ⟨_, _, h3⟩)
    · exact absurd ha (hd ha')
    · exact h3 hc
  · intro hr; exact Or.inr ⟨ha, (displays_mem hr).2, fun _ => hr⟩

/-- Swapping the two halves changes no triple. -/
lemma displays_swap (l r : Tree α) (a b c : α) :
    (node l r).Displays a b c ↔ (node r l).Displays a b c := by
  constructor <;>
  · rintro ⟨s, hs, h1, h2, h3⟩
    simp only [subtrees, List.mem_cons, List.mem_append] at hs
    rcases hs with rfl | hs | hs
    · refine ⟨_, self_mem_subtrees _, ?_, ?_, ?_⟩ <;> simp_all [Finset.union_comm]
    · exact ⟨s, by simp [subtrees, hs], h1, h2, h3⟩
    · exact ⟨s, by simp [subtrees, hs], h1, h2, h3⟩

lemma phylo_swap {l r : Tree α} : (node l r).Phylo ↔ (node r l).Phylo := by
  simp only [phylo_node]; constructor <;> rintro ⟨h1, h2, h3⟩ <;> exact ⟨h2, h1, h3.symm⟩

lemma agree_swap {l r T : Tree α} {Y : Finset α} :
    Agree (node l r) T Y ↔ Agree (node r l) T Y := by
  simp only [Agree, L_node, Finset.union_comm l.L, displays_swap l r]

lemma mast_swap (l r T : Tree α) : mast (node l r) T = mast (node r l) T :=
  le_antisymm (mast_le fun _ h => le_mast (agree_swap.1 h))
    (mast_le fun _ h => le_mast (agree_swap.2 h))

/-! ## The recursion, as lower bounds -/

/-- An agreement set inside the left half of `S` is an agreement set of `S` exactly when it is
one of the left half. -/
lemma agree_node_left_iff {l r T : Tree α} (h : (node l r).Phylo) {Y : Finset α}
    (hY : Y ⊆ l.L) : Agree (node l r) T Y ↔ Agree l T Y := by
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun x hx => Finset.mem_inter.2 ⟨hY hx, (Finset.mem_inter.1 (h1 hx)).2⟩,
      fun a ha b hb c hc => ?_⟩
    rw [← displays_node_of_left h (hY ha) (hY hc)]; exact h2 a ha b hb c hc
  · rintro ⟨h1, h2⟩
    refine ⟨fun x hx => ?_, fun a ha b hb c hc => ?_⟩
    · have := Finset.mem_inter.1 (h1 hx); simp [this.1, this.2]
    · rw [displays_node_of_left h (hY ha) (hY hc)]; exact h2 a ha b hb c hc

lemma agree_node_right_iff {l r T : Tree α} (h : (node l r).Phylo) {Y : Finset α}
    (hY : Y ⊆ r.L) : Agree (node l r) T Y ↔ Agree r T Y := by
  rw [agree_swap]; exact agree_node_left_iff (phylo_swap.1 h) hY

lemma mast_node_left {l r T : Tree α} (h : (node l r).Phylo) : mast l T ≤ mast (node l r) T := by
  obtain ⟨Y, hY, hc⟩ := exists_agree_mast l T
  rw [← hc]
  exact le_mast ((agree_node_left_iff h fun x hx => (Finset.mem_inter.1 (hY.1 hx)).1).2 hY)

lemma mast_node_right {l r T : Tree α} (h : (node l r).Phylo) :
    mast r T ≤ mast (node l r) T := by
  rw [mast_swap]; exact mast_node_left (phylo_swap.1 h)

/-- Agreement sets of matching halves combine. -/
lemma agree_merge {l r l' r' : Tree α} (hS : (node l r).Phylo) (hT : (node l' r').Phylo)
    {Y₁ Y₂ : Finset α} (h₁ : Agree l l' Y₁) (h₂ : Agree r r' Y₂) :
    Agree (node l r) (node l' r') (Y₁ ∪ Y₂) := by
  have dS := Finset.disjoint_left.1 (phylo_node.1 hS).2.2
  have dT := Finset.disjoint_left.1 (phylo_node.1 hT).2.2
  have m₁ : ∀ x ∈ Y₁, x ∈ l.L ∧ x ∈ l'.L := fun x hx => Finset.mem_inter.1 (h₁.1 hx)
  have m₂ : ∀ x ∈ Y₂, x ∈ r.L ∧ x ∈ r'.L := fun x hx => Finset.mem_inter.1 (h₂.1 hx)
  have e₁ : ∀ x ∈ Y₁ ∪ Y₂, (x ∈ l'.L ↔ x ∈ l.L) := by
    intro x hx
    rcases Finset.mem_union.1 hx with hx | hx
    · simp [(m₁ x hx).1, (m₁ x hx).2]
    · exact iff_of_false (fun h => dT h (m₂ x hx).2) (fun h => dS h (m₂ x hx).1)
  have e₂ : ∀ x ∈ Y₁ ∪ Y₂, (x ∈ r'.L ↔ x ∈ r.L) := by
    intro x hx
    rcases Finset.mem_union.1 hx with hx | hx
    · exact iff_of_false (fun h => dT (m₁ x hx).2 h) (fun h => dS (m₁ x hx).1 h)
    · simp [(m₂ x hx).1, (m₂ x hx).2]
  have i₁ : ∀ x ∈ Y₁ ∪ Y₂, x ∈ l.L → x ∈ Y₁ := by
    intro x hx hl
    rcases Finset.mem_union.1 hx with hx | hx
    · exact hx
    · exact absurd (m₂ x hx).1 (dS hl)
  have i₂ : ∀ x ∈ Y₁ ∪ Y₂, x ∈ r.L → x ∈ Y₂ := by
    intro x hx hr
    rcases Finset.mem_union.1 hx with hx | hx
    · exact absurd hr (dS (m₁ x hx).1)
    · exact hx
  refine ⟨fun x hx => ?_, fun a ha b hb c hc => ?_⟩
  · rcases Finset.mem_union.1 hx with hx | hx
    · simp [(m₁ x hx).1, (m₁ x hx).2]
    · simp [(m₂ x hx).1, (m₂ x hx).2]
  have hcS : c ∈ (node l r).L := by
    rcases Finset.mem_union.1 hc with hx | hx
    · simp [(m₁ c hx).1]
    · simp [(m₂ c hx).1]
  have hcT : c ∈ (node l' r').L := by
    rcases Finset.mem_union.1 hc with hx | hx
    · simp [(m₁ c hx).2]
    · simp [(m₂ c hx).2]
  rw [displays_node hcS, displays_node hcT, e₁ a ha, e₁ b hb, e₁ c hc, e₂ a ha, e₂ b hb,
    e₂ c hc]
  have k₁ : a ∈ l.L → b ∈ l.L → c ∈ l.L → (l.Displays a b c ↔ l'.Displays a b c) :=
    fun x y z => h₁.2 a (i₁ a ha x) b (i₁ b hb y) c (i₁ c hc z)
  have k₂ : a ∈ r.L → b ∈ r.L → c ∈ r.L → (r.Displays a b c ↔ r'.Displays a b c) :=
    fun x y z => h₂.2 a (i₂ a ha x) b (i₂ b hb y) c (i₂ c hc z)
  constructor
  · rintro (⟨x, y, z⟩ | ⟨x, y, z⟩)
    · exact Or.inl ⟨x, y, fun w => (k₁ x y w).1 (z w)⟩
    · exact Or.inr ⟨x, y, fun w => (k₂ x y w).1 (z w)⟩
  · rintro (⟨x, y, z⟩ | ⟨x, y, z⟩)
    · exact Or.inl ⟨x, y, fun w => (k₁ x y w).2 (z w)⟩
    · exact Or.inr ⟨x, y, fun w => (k₂ x y w).2 (z w)⟩

lemma mast_node_node {l r l' r' : Tree α} (hS : (node l r).Phylo) (hT : (node l' r').Phylo) :
    mast l l' + mast r r' ≤ mast (node l r) (node l' r') := by
  obtain ⟨Y₁, h₁, c₁⟩ := exists_agree_mast l l'
  obtain ⟨Y₂, h₂, c₂⟩ := exists_agree_mast r r'
  have hd : Disjoint Y₁ Y₂ := Finset.disjoint_left.2 fun x hx hx' =>
    Finset.disjoint_left.1 (phylo_node.1 hS).2.2 (Finset.mem_inter.1 (h₁.1 hx)).1
      (Finset.mem_inter.1 (h₂.1 hx')).1
  rw [← c₁, ← c₂, ← Finset.card_union_of_disjoint hd]
  exact le_mast (agree_merge hS hT h₁ h₂)

lemma mast_node_cross {l r l' r' : Tree α} (hS : (node l r).Phylo) (hT : (node l' r').Phylo) :
    mast l r' + mast r l' ≤ mast (node l r) (node l' r') := by
  have e : mast (node l r) (node r' l') = mast (node l r) (node l' r') :=
    (mast_comm _ _).trans ((mast_swap r' l' _).trans (mast_comm _ _))
  exact (mast_node_node hS (phylo_swap.1 hT)).trans_eq e

end Tree
end BalancedMast
