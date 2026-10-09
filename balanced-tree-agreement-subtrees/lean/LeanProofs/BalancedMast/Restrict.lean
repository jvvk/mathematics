import LeanProofs.BalancedMast.Basic

/-!
# Agreement sets are the sets with `S|Y ≅ T|Y`

The development uses agreement through displayed triples (`Tree.Agree`). This file shows that this
is the definition of the note: `Y` is an agreement set exactly when the restrictions `S|Y` and `T|Y`
(delete the leaves outside `Y`, suppress unary vertices) are isomorphic as leaf-labelled rooted
trees. The key step is that a rooted binary phylogenetic tree is determined by its triples
(`iso_of_triples`).
-/

namespace BalancedMast
namespace Tree

variable {α : Type*} [DecidableEq α]

/-- The restriction `S|Y`; `none` when `Y` misses `S`. -/
def restrict (Y : Finset α) : Tree α → Option (Tree α)
  | leaf x => if x ∈ Y then some (leaf x) else none
  | node l r =>
    match restrict Y l, restrict Y r with
    | some l', some r' => some (node l' r')
    | some l', none => some l'
    | none, r' => r'

/-- Isomorphism of leaf-labelled rooted binary trees: equality up to swapping children. -/
inductive Iso : Tree α → Tree α → Prop
  | leaf (x : α) : Iso (leaf x) (leaf x)
  | node {l r l' r' : Tree α} : Iso l l' → Iso r r' → Iso (node l r) (node l' r')
  | swap {l r l' r' : Tree α} : Iso l r' → Iso r l' → Iso (node l r) (node l' r')

/-- What restriction does to clusters and triples. -/
lemma restrict_spec (Y : Finset α) : ∀ S : Tree α, S.Phylo →
    (restrict Y S = none → ∀ x ∈ S.L, x ∉ Y) ∧
    ∀ R, restrict Y S = some R → R.L = S.L ∩ Y ∧ R.Phylo ∧
      ∀ a b c, a ∈ R.L → b ∈ R.L → c ∈ R.L → (R.Displays a b c ↔ S.Displays a b c) := by
  intro S
  induction S with
  | leaf x =>
    intro _
    by_cases hx : x ∈ Y
    · refine ⟨by simp [restrict, hx], fun R hR => ?_⟩
      simp only [restrict, hx, if_true, Option.some.injEq] at hR
      subst hR
      exact ⟨by simp [hx], by simp [Phylo, labels], fun _ _ _ _ _ _ => Iff.rfl⟩
    · refine ⟨fun _ y hy => by simp at hy; subst hy; exact hx, fun R hR => ?_⟩
      simp [restrict, hx] at hR
  | node l r ihl ihr =>
    intro pS
    obtain ⟨pl, pr, hd⟩ := phylo_node.1 pS
    have hd' := Finset.disjoint_left.1 hd
    obtain ⟨nl, sl⟩ := ihl pl
    obtain ⟨nr, sr⟩ := ihr pr
    rcases hl : restrict Y l with _ | l' <;> rcases hr : restrict Y r with _ | r'
    · refine ⟨fun _ x hx => ?_, fun R hR => by simp [restrict, hl, hr] at hR⟩
      simp only [L_node, Finset.mem_union] at hx
      rcases hx with hx | hx
      · exact nl hl x hx
      · exact nr hr x hx
    · obtain ⟨Lr, pr', tr⟩ := sr r' hr
      refine ⟨fun h => by simp [restrict, hl, hr] at h, fun R hR => ?_⟩
      simp only [restrict, hl, hr, Option.some.injEq] at hR
      subst hR
      refine ⟨?_, pr', fun a b c ha hb hc => ?_⟩
      · rw [Lr]; ext x; simp only [L_node, Finset.mem_inter, Finset.mem_union]
        constructor
        · rintro ⟨h1, h2⟩; exact ⟨Or.inr h1, h2⟩
        · rintro ⟨h1 | h1, h2⟩
          · exact absurd h2 (nl hl x h1)
          · exact ⟨h1, h2⟩
      · have hR : ∀ x ∈ r'.L, x ∈ r.L := fun x hx => by
          rw [Lr] at hx; exact (Finset.mem_inter.1 hx).1
        rw [tr a b c ha hb hc, displays_node_of_right pS (hR a ha) (hR c hc)]
    · obtain ⟨Ll, pl', tl⟩ := sl l' hl
      refine ⟨fun h => by simp [restrict, hl, hr] at h, fun R hR => ?_⟩
      simp only [restrict, hl, hr, Option.some.injEq] at hR
      subst hR
      refine ⟨?_, pl', fun a b c ha hb hc => ?_⟩
      · rw [Ll]; ext x; simp only [L_node, Finset.mem_inter, Finset.mem_union]
        constructor
        · rintro ⟨h1, h2⟩; exact ⟨Or.inl h1, h2⟩
        · rintro ⟨h1 | h1, h2⟩
          · exact ⟨h1, h2⟩
          · exact absurd h2 (nr hr x h1)
      · have hR : ∀ x ∈ l'.L, x ∈ l.L := fun x hx => by
          rw [Ll] at hx; exact (Finset.mem_inter.1 hx).1
        rw [tl a b c ha hb hc, displays_node_of_left pS (hR a ha) (hR c hc)]
    · obtain ⟨Ll, pl', tl⟩ := sl l' hl
      obtain ⟨Lr, pr', tr⟩ := sr r' hr
      refine ⟨fun h => by simp [restrict, hl, hr] at h, fun R hR => ?_⟩
      simp only [restrict, hl, hr, Option.some.injEq] at hR
      subst hR
      have mem_l : ∀ x, x ∈ l'.L ↔ x ∈ l.L ∧ x ∈ Y := fun x => by rw [Ll, Finset.mem_inter]
      have mem_r : ∀ x, x ∈ r'.L ↔ x ∈ r.L ∧ x ∈ Y := fun x => by rw [Lr, Finset.mem_inter]
      refine ⟨?_, phylo_node.2 ⟨pl', pr', ?_⟩, fun a b c ha hb hc => ?_⟩
      · ext x; simp only [L_node, Finset.mem_union, Finset.mem_inter, mem_l, mem_r]; tauto
      · exact Finset.disjoint_left.2 fun x h1 h2 => hd' ((mem_l x).1 h1).1 ((mem_r x).1 h2).1
      · have hY : ∀ x ∈ (node l' r').L, x ∈ Y := fun x hx => by
          simp only [L_node, Finset.mem_union, mem_l, mem_r] at hx; tauto
        have hcS : c ∈ (node l r).L := by
          simp only [L_node, Finset.mem_union, mem_l, mem_r] at hc ⊢; tauto
        rw [displays_node hc, displays_node hcS, mem_l, mem_l, mem_l, mem_r, mem_r, mem_r]
        have ya := hY a ha; have yb := hY b hb; have yc := hY c hc
        constructor
        · rintro (⟨⟨h1, _⟩, ⟨h2, _⟩, h3⟩ | ⟨⟨h1, _⟩, ⟨h2, _⟩, h3⟩)
          · refine Or.inl ⟨h1, h2, fun h => ?_⟩
            exact (tl a b c ((mem_l a).2 ⟨h1, ya⟩) ((mem_l b).2 ⟨h2, yb⟩)
              ((mem_l c).2 ⟨h, yc⟩)).1 (h3 ⟨h, yc⟩)
          · refine Or.inr ⟨h1, h2, fun h => ?_⟩
            exact (tr a b c ((mem_r a).2 ⟨h1, ya⟩) ((mem_r b).2 ⟨h2, yb⟩)
              ((mem_r c).2 ⟨h, yc⟩)).1 (h3 ⟨h, yc⟩)
        · rintro (⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩)
          · refine Or.inl ⟨⟨h1, ya⟩, ⟨h2, yb⟩, fun h => ?_⟩
            exact (tl a b c ((mem_l a).2 ⟨h1, ya⟩) ((mem_l b).2 ⟨h2, yb⟩)
              ((mem_l c).2 h)).2 (h3 h.1)
          · refine Or.inr ⟨⟨h1, ya⟩, ⟨h2, yb⟩, fun h => ?_⟩
            exact (tr a b c ((mem_r a).2 ⟨h1, ya⟩) ((mem_r b).2 ⟨h2, yb⟩)
              ((mem_r c).2 h)).2 (h3 h.1)

/-- Isomorphic trees have the same clusters and display the same triples. -/
lemma Iso.triples {R R' : Tree α} (h : Iso R R') :
    R.L = R'.L ∧ ∀ a b c, c ∈ R.L → (R.Displays a b c ↔ R'.Displays a b c) := by
  induction h with
  | leaf x => exact ⟨rfl, fun _ _ _ _ => Iff.rfl⟩
  | @node l r l' r' _ _ ihl ihr =>
    refine ⟨by simp [ihl.1, ihr.1], fun a b c hc => ?_⟩
    have hc' : c ∈ (Tree.node l' r').L := by simpa [← ihl.1, ← ihr.1] using hc
    rw [displays_node hc, displays_node hc', ← ihl.1, ← ihr.1]
    constructor
    · rintro (⟨x, y, z⟩ | ⟨x, y, z⟩)
      · exact Or.inl ⟨x, y, fun w => (ihl.2 a b c w).1 (z w)⟩
      · exact Or.inr ⟨x, y, fun w => (ihr.2 a b c w).1 (z w)⟩
    · rintro (⟨x, y, z⟩ | ⟨x, y, z⟩)
      · exact Or.inl ⟨x, y, fun w => (ihl.2 a b c w).2 (z w)⟩
      · exact Or.inr ⟨x, y, fun w => (ihr.2 a b c w).2 (z w)⟩
  | @swap l r l' r' _ _ ihl ihr =>
    refine ⟨by simp [ihl.1, ihr.1, Finset.union_comm], fun a b c hc => ?_⟩
    have hc' : c ∈ (Tree.node l' r').L := by
      simp only [L_node, Finset.mem_union] at hc ⊢; rw [← ihl.1, ← ihr.1]; tauto
    rw [displays_node hc, displays_node hc', ← ihl.1, ← ihr.1]
    constructor
    · rintro (⟨x, y, z⟩ | ⟨x, y, z⟩)
      · exact Or.inr ⟨x, y, fun w => (ihl.2 a b c w).1 (z w)⟩
      · exact Or.inl ⟨x, y, fun w => (ihr.2 a b c w).1 (z w)⟩
    · rintro (⟨x, y, z⟩ | ⟨x, y, z⟩)
      · exact Or.inr ⟨x, y, fun w => (ihr.2 a b c w).2 (z w)⟩
      · exact Or.inl ⟨x, y, fun w => (ihl.2 a b c w).2 (z w)⟩

lemma two_le_card_node {l r : Tree α} (h : (node l r).Phylo) : 2 ≤ (node l r).L.card := by
  rw [L_node, Finset.card_union_of_disjoint (phylo_node.1 h).2.2]
  have := l.L_nonempty.card_pos; have := r.L_nonempty.card_pos; omega

/-- The root split is determined by the triples. -/
lemma root_split {l r l' r' : Tree α} (pS : (node l r).Phylo) (pT : (node l' r').Phylo)
    (hL : (node l r).L = (node l' r').L)
    (ht : ∀ a ∈ (node l r).L, ∀ b ∈ (node l r).L, ∀ c ∈ (node l r).L,
      ((node l r).Displays a b c ↔ (node l' r').Displays a b c))
    {x : α} (hx : x ∈ l.L) (hx' : x ∈ l'.L) : l.L = l'.L ∧ r.L = r'.L := by
  have dS := Finset.disjoint_left.1 (phylo_node.1 pS).2.2
  have dT := Finset.disjoint_left.1 (phylo_node.1 pT).2.2
  have mem : ∀ y, y ∈ l.L ∨ y ∈ r.L ↔ y ∈ l'.L ∨ y ∈ r'.L := fun y => by
    have := congrArg (y ∈ ·) hL; simpa using this
  obtain ⟨z, hz⟩ := r.L_nonempty
  obtain ⟨z', hz'⟩ := r'.L_nonempty
  have inS : ∀ y, y ∈ (node l r).L ↔ y ∈ l.L ∨ y ∈ r.L := by simp
  have hll : l.L = l'.L := by
    ext y; constructor
    · intro hy
      rcases (mem y).1 (Or.inl hy) with h | h
      · exact h
      · exfalso
        have hS : (node l r).Displays x y z := by
          rw [displays_node (by simp [hz])]; exact Or.inl ⟨hx, hy, fun h => absurd hz (dS h)⟩
        have hT := (ht x ((inS x).2 (Or.inl hx)) y ((inS y).2 (Or.inl hy)) z
          ((inS z).2 (Or.inr hz))).1 hS
        rw [displays_node (by rw [← hL]; simp [hz])] at hT
        rcases hT with ⟨_, h2, _⟩ | ⟨h1, _, _⟩
        · exact dT h2 h
        · exact dT hx' h1
    · intro hy
      rcases (mem y).2 (Or.inl hy) with h | h
      · exact h
      · exfalso
        have hT : (node l' r').Displays x y z' := by
          rw [displays_node (by simp [hz'])]
          exact Or.inl ⟨hx', hy, fun h => absurd hz' (dT h)⟩
        have hS := (ht x ((inS x).2 (Or.inl hx)) y ((inS y).2 (Or.inr h)) z'
          (by rw [hL]; simp [hz'])).2 hT
        rw [displays_node (by rw [hL]; simp [hz'])] at hS
        rcases hS with ⟨_, h2, _⟩ | ⟨h1, _, _⟩
        · exact dS h2 h
        · exact dS hx h1
  refine ⟨hll, ?_⟩
  ext y; constructor
  · intro hy
    rcases (mem y).1 (Or.inr hy) with h | h
    · rw [← hll] at h; exact absurd hy (dS h)
    · exact h
  · intro hy
    rcases (mem y).2 (Or.inr hy) with h | h
    · rw [hll] at h; exact absurd hy (dT h)
    · exact h

/-- **A rooted binary phylogenetic tree is determined by its triples.** -/
theorem iso_of_triples : ∀ (R R' : Tree α), R.Phylo → R'.Phylo → R.L = R'.L →
    (∀ a ∈ R.L, ∀ b ∈ R.L, ∀ c ∈ R.L, (R.Displays a b c ↔ R'.Displays a b c)) → Iso R R' := by
  intro R
  induction R with
  | leaf x =>
    intro R' _ pR' hL _
    cases R' with
    | leaf y => simp at hL; subst hL; exact Iso.leaf x
    | node l r => have := two_le_card_node pR'; rw [← hL] at this; simp at this
  | node l r ihl ihr =>
    intro R' pR pR' hL ht
    cases R' with
    | leaf y => have := two_le_card_node pR; rw [hL] at this; simp at this
    | node l' r' =>
      obtain ⟨pl, pr, _⟩ := phylo_node.1 pR
      obtain ⟨pl', pr', _⟩ := phylo_node.1 pR'
      obtain ⟨x, hx⟩ := l.L_nonempty
      have hxT : x ∈ l'.L ∨ x ∈ r'.L := by
        have := congrArg (x ∈ ·) hL; simp only [L_node, Finset.mem_union] at this
        exact Eq.mp this (Or.inl hx)
      have inR : ∀ y, y ∈ (node l r).L ↔ y ∈ l.L ∨ y ∈ r.L := by simp
      -- triples inside a half of `R` are those of `R`, hence of `R'`
      have half : ∀ (u u' : Tree α), u.L = u'.L →
          (∀ a b c, a ∈ u.L → c ∈ u.L → ((node l r).Displays a b c ↔ u.Displays a b c)) →
          (∀ a b c, a ∈ u'.L → c ∈ u'.L → ((node l' r').Displays a b c ↔ u'.Displays a b c)) →
          (∀ y ∈ u.L, y ∈ (node l r).L) →
          ∀ a ∈ u.L, ∀ b ∈ u.L, ∀ c ∈ u.L, (u.Displays a b c ↔ u'.Displays a b c) := by
        intro u u' huL hu hu' hsub a ha b hb c hc
        rw [← hu a b c ha hc, ← hu' a b c (huL ▸ ha) (huL ▸ hc)]
        exact ht a (hsub a ha) b (hsub b hb) c (hsub c hc)
      rcases hxT with hx' | hx'
      · obtain ⟨e₁, e₂⟩ := root_split pR pR' hL ht hx hx'
        refine Iso.node (ihl l' pl pl' e₁ (half l l' e₁ (fun a b c ha hc =>
          displays_node_of_left pR ha hc) (fun a b c ha hc => displays_node_of_left pR' ha hc)
          fun y hy => (inR y).2 (Or.inl hy))) (ihr r' pr pr' e₂ (half r r' e₂
          (fun a b c ha hc => displays_node_of_right pR ha hc)
          (fun a b c ha hc => displays_node_of_right pR' ha hc)
          fun y hy => (inR y).2 (Or.inr hy)))
      · have pR'' := phylo_swap.1 pR'
        have hL' : (node l r).L = (node r' l').L := by rw [hL]; simp [Finset.union_comm]
        have ht' : ∀ a ∈ (node l r).L, ∀ b ∈ (node l r).L, ∀ c ∈ (node l r).L,
            ((node l r).Displays a b c ↔ (node r' l').Displays a b c) :=
          fun a ha b hb c hc => (ht a ha b hb c hc).trans (displays_swap _ _ _ _ _)
        obtain ⟨e₁, e₂⟩ := root_split pR pR'' hL' ht' hx hx'
        refine Iso.swap (ihl r' pl pr' e₁ (half l r' e₁ (fun a b c ha hc =>
          displays_node_of_left pR ha hc)
          (fun a b c ha hc => displays_node_of_right pR' ha hc)
          fun y hy => (inR y).2 (Or.inl hy))) (ihr l' pr pl' e₂ (half r l' e₂
          (fun a b c ha hc => displays_node_of_right pR ha hc)
          (fun a b c ha hc => displays_node_of_left pR' ha hc)
          fun y hy => (inR y).2 (Or.inr hy)))

/-- **Agreement sets are the sets on which the restrictions are isomorphic.** -/
theorem agree_iff_restrict_iso {S T : Tree α} (pS : S.Phylo) (pT : T.Phylo) {Y : Finset α}
    (hY : Y ⊆ S.L ∩ T.L) (hne : Y.Nonempty) :
    Agree S T Y ↔ ∃ R R', restrict Y S = some R ∧ restrict Y T = some R' ∧ Iso R R' := by
  obtain ⟨y, hy⟩ := hne
  have hyS := (Finset.mem_inter.1 (hY hy)).1
  have hyT := (Finset.mem_inter.1 (hY hy)).2
  obtain ⟨nS, sS⟩ := restrict_spec Y S pS
  obtain ⟨nT, sT⟩ := restrict_spec Y T pT
  obtain ⟨R, hR⟩ : ∃ R, restrict Y S = some R := by
    rcases h : restrict Y S with _ | R
    · exact absurd hy (nS h y hyS)
    · exact ⟨R, rfl⟩
  obtain ⟨R', hR'⟩ : ∃ R', restrict Y T = some R' := by
    rcases h : restrict Y T with _ | R'
    · exact absurd hy (nT h y hyT)
    · exact ⟨R', rfl⟩
  obtain ⟨LR, pR, tR⟩ := sS R hR
  obtain ⟨LR', pR', tR'⟩ := sT R' hR'
  have eR : R.L = Y := by
    rw [LR]; exact Finset.inter_eq_right.2 fun x hx => (Finset.mem_inter.1 (hY hx)).1
  have eR' : R'.L = Y := by
    rw [LR']; exact Finset.inter_eq_right.2 fun x hx => (Finset.mem_inter.1 (hY hx)).2
  constructor
  · intro hA
    refine ⟨R, R', hR, hR', iso_of_triples R R' pR pR' (eR.trans eR'.symm) ?_⟩
    intro a ha b hb c hc
    rw [eR] at ha hb hc
    rw [tR a b c (eR ▸ ha) (eR ▸ hb) (eR ▸ hc), tR' a b c (eR' ▸ ha) (eR' ▸ hb) (eR' ▸ hc)]
    exact hA.2 a ha b hb c hc
  · rintro ⟨R₁, R₁', h₁, h₁', hiso⟩
    rw [hR] at h₁; rw [hR'] at h₁'
    cases h₁; cases h₁'
    refine ⟨hY, fun a ha b hb c hc => ?_⟩
    rw [← tR a b c (eR ▸ ha) (eR ▸ hb) (eR ▸ hc), ← tR' a b c (eR' ▸ ha) (eR' ▸ hb) (eR' ▸ hc)]
    exact hiso.triples.2 a b c (eR ▸ hc)

end Tree
end BalancedMast
