import LeanProofs.BalancedMast.Balanced

/-!
# The grid bound (Bordewich et al., Lemma 4.5)

Cut `S` at depth `dS` and `T` at depth `dT` into blocks. If no cell `L(s) ∩ L(t)` holds an
agreement set of size three, then `mast(S, T) ≤ 2 · max(2^dS, 2^dT)`.

The proof follows theirs: an agreement set that uses one half of `S` on both halves of `T`
cannot use the other half of `S` (cases (A)–(D)), so it lies in one half of a tree, or in two
diagonal (or two anti-diagonal) quarters.
-/

namespace BalancedMast
namespace Tree

variable {α : Type*} [DecidableEq α]

/-- The pendant subtrees at depth `d`; a leaf above depth `d` is its own block. -/
def blocks : ℕ → Tree α → List (Tree α)
  | 0, S => [S]
  | _ + 1, leaf a => [leaf a]
  | d + 1, node l r => blocks d l ++ blocks d r

lemma mem_subtrees_of_mem_blocks {d : ℕ} {S s : Tree α} (h : s ∈ blocks d S) :
    s ∈ S.subtrees := by
  induction d generalizing S with
  | zero => simp [blocks] at h; subst h; exact self_mem_subtrees _
  | succ d ih =>
    cases S with
    | leaf a => simp [blocks] at h; subst h; exact self_mem_subtrees _
    | node l r =>
      simp only [blocks, List.mem_append] at h
      rcases h with h | h
      · simp [subtrees, ih h]
      · simp [subtrees, ih h]

lemma blocks_bind {β : Type*} [DecidableEq β] {d : ℕ} {S : Tree β} {A : β → Tree α}
    (hS : Bal d S) : blocks d (S.bind A) = S.labels.map A := by
  induction hS with
  | leaf a => simp [blocks, Tree.bind, labels]
  | node _ _ ihl ihr => simp [blocks, Tree.bind, labels, ihl, ihr]

/-- No cell holds three labels on which the two trees agree. -/
def CellsSmall (S T : Tree α) (dS dT : ℕ) : Prop :=
  ∀ s ∈ blocks dS S, ∀ t ∈ blocks dT T, ∀ Y ⊆ s.L ∩ t.L, Agree S T Y → Y.card ≤ 2

lemma agree_node_left_iff' {S l r : Tree α} (h : (node l r).Phylo) {Y : Finset α}
    (hY : Y ⊆ l.L) : Agree S (node l r) Y ↔ Agree S l Y :=
  ⟨fun h' => ((agree_node_left_iff h hY).1 h'.symm).symm,
    fun h' => ((agree_node_left_iff h hY).2 h'.symm).symm⟩

lemma agree_node_right_iff' {S l r : Tree α} (h : (node l r).Phylo) {Y : Finset α}
    (hY : Y ⊆ r.L) : Agree S (node l r) Y ↔ Agree S r Y :=
  ⟨fun h' => ((agree_node_right_iff h hY).1 h'.symm).symm,
    fun h' => ((agree_node_right_iff h hY).2 h'.symm).symm⟩

lemma CellsSmall.left {l r T : Tree α} {d dT : ℕ} (hS : (node l r).Phylo)
    (h : CellsSmall (node l r) T (d + 1) dT) : CellsSmall l T d dT := by
  intro s hs t ht Y hY hA
  have hsl : s.L ⊆ l.L := L_subset_of_mem_subtrees (mem_subtrees_of_mem_blocks hs)
  refine h s (by simp [blocks, hs]) t ht Y hY ((agree_node_left_iff hS ?_).2 hA)
  exact fun x hx => hsl (Finset.mem_inter.1 (hY hx)).1

lemma CellsSmall.right {l r T : Tree α} {d dT : ℕ} (hS : (node l r).Phylo)
    (h : CellsSmall (node l r) T (d + 1) dT) : CellsSmall r T d dT := by
  intro s hs t ht Y hY hA
  have hsr : s.L ⊆ r.L := L_subset_of_mem_subtrees (mem_subtrees_of_mem_blocks hs)
  refine h s (by simp [blocks, hs]) t ht Y hY ((agree_node_right_iff hS ?_).2 hA)
  exact fun x hx => hsr (Finset.mem_inter.1 (hY hx)).1

lemma CellsSmall.symm {S T : Tree α} {dS dT : ℕ} (h : CellsSmall S T dS dT) :
    CellsSmall T S dT dS := fun t ht s hs Y hY hA =>
  h s hs t ht Y (by rw [Finset.inter_comm]; exact hY) hA.symm

/-- Splitting one tree at its root: the two halves of an agreement set. -/
lemma card_split {l r T : Tree α} (hS : (node l r).Phylo) {Y : Finset α}
    (hY : Agree (node l r) T Y) :
    Y.card = (Y.filter (· ∈ l.L)).card + (Y.filter (· ∈ r.L)).card ∧
      Agree l T (Y.filter (· ∈ l.L)) ∧ Agree r T (Y.filter (· ∈ r.L)) := by
  have hd := Finset.disjoint_left.1 (phylo_node.1 hS).2.2
  refine ⟨?_, (agree_node_left_iff hS fun x hx => (Finset.mem_filter.1 hx).2).1
      (hY.mono (Finset.filter_subset _ _)),
    (agree_node_right_iff hS fun x hx => (Finset.mem_filter.1 hx).2).1
      (hY.mono (Finset.filter_subset _ _))⟩
  rw [← Finset.card_union_of_disjoint]
  · congr 1; ext x
    simp only [Finset.mem_union, Finset.mem_filter]
    constructor
    · intro hx
      have := (Finset.mem_inter.1 (hY.1 hx)).1
      simp only [L_node, Finset.mem_union] at this
      tauto
    · rintro (⟨hx, _⟩ | ⟨hx, _⟩) <;> exact hx
  · exact Finset.disjoint_left.2 fun x hx hx' =>
      hd (Finset.mem_filter.1 hx).2 (Finset.mem_filter.1 hx').2

/-- Case (A) of Lemma 4.5: if an agreement set has `x ∈ S_L ∩ T_L` and `y ∈ S_L ∩ T_R`, it has
no label in `S_R`, since `S` displays `xy|z` and `T` does not. -/
lemma no_split {l r l' r' : Tree α} (hT : (node l' r').Phylo) {Y : Finset α}
    (hY : Agree (node l r) (node l' r') Y) {x y z : α} (hx : x ∈ Y) (hy : y ∈ Y) (hz : z ∈ Y)
    (hxl : x ∈ l.L) (hyl : y ∈ l.L) (hzr : z ∈ r.L) (hzl : z ∉ l.L) (hxl' : x ∈ l'.L)
    (hyr' : y ∈ r'.L) : False := by
  have hdT := Finset.disjoint_left.1 (phylo_node.1 hT).2.2
  have hS : (node l r).Displays x y z := by
    rw [displays_node (by simp [hzr])]; exact Or.inl ⟨hxl, hyl, fun h => absurd h hzl⟩
  have hzT : z ∈ (node l' r').L := (Finset.mem_inter.1 (hY.1 hz)).2
  have hT' := (hY.2 x hx y hy z hz).1 hS
  rw [displays_node hzT] at hT'
  rcases hT' with ⟨_, hy', _⟩ | ⟨hx', _, _⟩
  · exact hdT hy' hyr'
  · exact hdT hxl' hx'

/-- **Lemma 4.5 of Bordewich et al.** -/
theorem card_le_of_cellsSmall (n : ℕ) : ∀ (dS dT : ℕ), dS + dT = n → ∀ S T : Tree α,
    S.Phylo → T.Phylo → CellsSmall S T dS dT → ∀ Y, Agree S T Y →
    Y.card ≤ 2 * max (2 ^ dS) (2 ^ dT) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro dS dT hn S T pS pT hC Y hY
  have hYS : Y.card ≤ S.L.card := Finset.card_le_card fun x hx => (Finset.mem_inter.1 (hY.1 hx)).1
  have hYT : Y.card ≤ T.L.card := Finset.card_le_card fun x hx => (Finset.mem_inter.1 (hY.1 hx)).2
  have one_le : 1 ≤ max (2 ^ dS) (2 ^ dT) := le_max_of_le_left (Nat.one_le_two_pow)
  -- a leaf carries one label
  cases S with
  | leaf a => simp at hYS; omega
  | node l r =>
  cases T with
  | leaf a => simp at hYT; omega
  | node l' r' =>
  obtain ⟨pl, pr, hdS⟩ := phylo_node.1 pS
  obtain ⟨pl', pr', hdT⟩ := phylo_node.1 pT
  have two_pos' : 0 < 2 := by norm_num
  rcases Nat.eq_zero_or_pos dS with hS0 | hS0 <;> rcases Nat.eq_zero_or_pos dT with hT0 | hT0
  · -- both depths zero: the whole of `Y` is one cell
    subst hS0; subst hT0
    simpa using hC _ (by simp [blocks]) _ (by simp [blocks]) Y hY.1 hY
  · -- split `T`
    subst hS0
    obtain ⟨e, rfl⟩ : ∃ e, dT = e + 1 := ⟨dT - 1, by omega⟩
    have hC' := hC.symm
    obtain ⟨hc, h₁, h₂⟩ := card_split pT hY.symm
    have b₁ := ih (e + 0) (by omega) e 0 rfl l' _ pl' pS (hC'.left pT) _ h₁
    have b₂ := ih (e + 0) (by omega) e 0 rfl r' _ pr' pS (hC'.right pT) _ h₂
    have m₁ : max (2 ^ e) (2 ^ 0) = 2 ^ e := max_eq_left Nat.one_le_two_pow
    have m₂ : max (2 ^ 0) (2 ^ (e + 1)) = 2 ^ (e + 1) := max_eq_right Nat.one_le_two_pow
    rw [m₁] at b₁ b₂; rw [m₂, hc, pow_succ]; omega
  · -- split `S`
    subst hT0
    obtain ⟨d, rfl⟩ : ∃ d, dS = d + 1 := ⟨dS - 1, by omega⟩
    obtain ⟨hc, h₁, h₂⟩ := card_split pS hY
    have b₁ := ih (d + 0) (by omega) d 0 rfl l _ pl pT (hC.left pS) _ h₁
    have b₂ := ih (d + 0) (by omega) d 0 rfl r _ pr pT (hC.right pS) _ h₂
    have m₁ : max (2 ^ d) (2 ^ 0) = 2 ^ d := max_eq_left Nat.one_le_two_pow
    have m₂ : max (2 ^ (d + 1)) (2 ^ 0) = 2 ^ (d + 1) := max_eq_left Nat.one_le_two_pow
    rw [m₁] at b₁ b₂; rw [m₂, hc, pow_succ]; omega
  · -- both depths positive: Bordewich et al.'s cases
    obtain ⟨d, rfl⟩ : ∃ d, dS = d + 1 := ⟨dS - 1, by omega⟩
    obtain ⟨e, rfl⟩ : ∃ e, dT = e + 1 := ⟨dT - 1, by omega⟩
    have hmax : 2 * max (2 ^ d) (2 ^ e) = max (2 ^ (d + 1)) (2 ^ (e + 1)) := by
      rcases le_total d e with h | h
      · rw [max_eq_right (Nat.pow_le_pow_right two_pos' h),
          max_eq_right (Nat.pow_le_pow_right two_pos' (by omega : d + 1 ≤ e + 1))]; ring
      · rw [max_eq_left (Nat.pow_le_pow_right two_pos' h),
          max_eq_left (Nat.pow_le_pow_right two_pos' (by omega : e + 1 ≤ d + 1))]; ring
    have hmono : max (2 ^ d) (2 ^ (e + 1)) ≤ max (2 ^ (d + 1)) (2 ^ (e + 1)) :=
      max_le_max (Nat.pow_le_pow_right two_pos' (by omega)) le_rfl
    have hmono' : max (2 ^ (d + 1)) (2 ^ e) ≤ max (2 ^ (d + 1)) (2 ^ (e + 1)) :=
      max_le_max le_rfl (Nat.pow_le_pow_right two_pos' (by omega))
    have mS : ∀ x ∈ Y, x ∈ l.L ∨ x ∈ r.L := fun x hx => by
      simpa using (Finset.mem_inter.1 (hY.1 hx)).1
    have mT : ∀ x ∈ Y, x ∈ l'.L ∨ x ∈ r'.L := fun x hx => by
      simpa using (Finset.mem_inter.1 (hY.1 hx)).2
    have dS' := Finset.disjoint_left.1 hdS
    have dT' := Finset.disjoint_left.1 hdT
    -- (I): `Y` misses a half of `S`
    by_cases hr : ∀ x ∈ Y, x ∉ r.L
    · have hYl : Y ⊆ l.L := fun x hx => (mS x hx).resolve_right (hr x hx)
      have := ih (d + (e + 1)) (by omega) d (e + 1) rfl l _ pl pT (hC.left pS) Y
        ((agree_node_left_iff pS hYl).1 hY)
      omega
    by_cases hl : ∀ x ∈ Y, x ∉ l.L
    · have hYr : Y ⊆ r.L := fun x hx => (mS x hx).resolve_left (hl x hx)
      have := ih (d + (e + 1)) (by omega) d (e + 1) rfl r _ pr pT (hC.right pS) Y
        ((agree_node_right_iff pS hYr).1 hY)
      omega
    -- (II): `Y` misses a half of `T`
    by_cases hr' : ∀ x ∈ Y, x ∉ r'.L
    · have hYl : Y ⊆ l'.L := fun x hx => (mT x hx).resolve_right (hr' x hx)
      have := ih (e + (d + 1)) (by omega) e (d + 1) rfl l' _ pl' pS (hC.symm.left pT) Y
        ((agree_node_left_iff' pT hYl).1 hY).symm
      rw [max_comm] at this; omega
    by_cases hl' : ∀ x ∈ Y, x ∉ l'.L
    · have hYr : Y ⊆ r'.L := fun x hx => (mT x hx).resolve_left (hl' x hx)
      have := ih (e + (d + 1)) (by omega) e (d + 1) rfl r' _ pr' pS (hC.symm.right pT) Y
        ((agree_node_right_iff' pT hYr).1 hY).symm
      rw [max_comm] at this; omega
    push_neg at hr hl hr' hl'
    obtain ⟨zr, hzr, hzr'⟩ := hr
    obtain ⟨zl, hzl, hzl'⟩ := hl
    obtain ⟨zr2, hzr2, hzr2'⟩ := hr'
    obtain ⟨zl2, hzl2, hzl2'⟩ := hl'
    -- the four symmetric forms of case (A)
    have A : ∀ x ∈ Y, ∀ y ∈ Y, x ∈ l.L → y ∈ l.L → x ∈ l'.L → y ∈ r'.L → False :=
      fun x hx y hy h1 h2 h3 h4 =>
        no_split pT hY hx hy hzr h1 h2 hzr' (fun h => dS' h hzr') h3 h4
    have B : ∀ x ∈ Y, ∀ y ∈ Y, x ∈ r.L → y ∈ r.L → x ∈ l'.L → y ∈ r'.L → False :=
      fun x hx y hy h1 h2 h3 h4 =>
        no_split pT (agree_swap.1 hY) hx hy hzl h1 h2 hzl' (fun h => dS' hzl' h) h3 h4
    have C : ∀ x ∈ Y, ∀ y ∈ Y, x ∈ l'.L → y ∈ l'.L → x ∈ l.L → y ∈ r.L → False :=
      fun x hx y hy h1 h2 h3 h4 =>
        no_split pS hY.symm hx hy hzr2 h1 h2 hzr2' (fun h => dT' h hzr2') h3 h4
    have D : ∀ x ∈ Y, ∀ y ∈ Y, x ∈ r'.L → y ∈ r'.L → x ∈ l.L → y ∈ r.L → False :=
      fun x hx y hy h1 h2 h3 h4 =>
        no_split pS (agree_swap.1 hY.symm) hx hy hzl2 h1 h2 hzl2' (fun h => dT' hzl2' h) h3 h4
    -- (III): `Y` lies on the diagonal or on the anti-diagonal
    let Y₁ := Y.filter (· ∈ l.L)
    let Y₂ := Y.filter (· ∈ r.L)
    have hc : Y.card = Y₁.card + Y₂.card := (card_split pS hY).1
    have quarter : ∀ (a b : Tree α), a.Phylo → b.Phylo →
        CellsSmall a b d e → ∀ Z, Agree a b Z → Z.card ≤ 2 * max (2 ^ d) (2 ^ e) :=
      fun a b pa pb hab Z hZ => ih (d + e) (by omega) d e rfl a b pa pb hab Z hZ
    by_cases hdiag : ∀ x ∈ Y, (x ∈ l.L ↔ x ∈ l'.L)
    · -- diagonal: `Y₁ ⊆ S_L ∩ T_L` and `Y₂ ⊆ S_R ∩ T_R`
      have h₁ : Agree l l' Y₁ := by
        refine (agree_node_left_iff' pT fun x hx => ?_).1 (card_split pS hY).2.1
        exact (hdiag x (Finset.mem_filter.1 hx).1).1 (Finset.mem_filter.1 hx).2
      have h₂ : Agree r r' Y₂ := by
        refine (agree_node_right_iff' pT fun x hx => ?_).1 (card_split pS hY).2.2
        obtain ⟨hxY, hxr⟩ := Finset.mem_filter.1 hx
        exact (mT x hxY).resolve_left fun h => dS' ((hdiag x hxY).2 h) hxr
      have c₁ := quarter l l' pl pl' ((hC.left pS).symm.left pT).symm Y₁ h₁
      have c₂ := quarter r r' pr pr' ((hC.right pS).symm.right pT).symm Y₂ h₂
      omega
    · -- anti-diagonal: `Y₁ ⊆ S_L ∩ T_R` and `Y₂ ⊆ S_R ∩ T_L`
      push_neg at hdiag
      have anti : ∀ x ∈ Y, (x ∈ l.L ↔ x ∈ r'.L) := by
        obtain ⟨w, hw, hw'⟩ := hdiag
        intro x hx
        rcases mS x hx with hxl | hxr <;> rcases mT x hx with hxl' | hxr'
        · -- `x ∈ S_L ∩ T_L` together with an off-diagonal `w`
          exfalso
          rcases hw' with ⟨hwl, hwl'⟩ | ⟨hwl, hwl'⟩
          · exact A x hx w hw hxl hwl hxl' ((mT w hw).resolve_left hwl')
          · exact C x hx w hw hxl' hwl' hxl ((mS w hw).resolve_left hwl)
        · exact iff_of_true hxl hxr'
        · exact iff_of_false (fun h => dS' h hxr) (fun h => dT' hxl' h)
        · exfalso
          rcases hw' with ⟨hwl, hwl'⟩ | ⟨hwl, hwl'⟩
          · exact D w hw x hx ((mT w hw).resolve_left hwl') hxr' hwl hxr
          · exact B w hw x hx ((mS w hw).resolve_left hwl) hxr hwl' hxr'
      have h₁ : Agree l r' Y₁ := by
        refine (agree_node_right_iff' pT fun x hx => ?_).1 (card_split pS hY).2.1
        exact (anti x (Finset.mem_filter.1 hx).1).1 (Finset.mem_filter.1 hx).2
      have h₂ : Agree r l' Y₂ := by
        refine (agree_node_left_iff' pT fun x hx => ?_).1 (card_split pS hY).2.2
        obtain ⟨hxY, hxr⟩ := Finset.mem_filter.1 hx
        exact (mT x hxY).resolve_right fun h => dS' ((anti x hxY).2 h) hxr
      have c₁ := quarter l r' pl pr' ((hC.left pS).symm.right pT).symm Y₁ h₁
      have c₂ := quarter r l' pr pl' ((hC.right pS).symm.left pT).symm Y₂ h₂
      omega

theorem mast_le_of_cellsSmall {S T : Tree α} {dS dT : ℕ} (pS : S.Phylo) (pT : T.Phylo)
    (h : CellsSmall S T dS dT) : mast S T ≤ 2 * max (2 ^ dS) (2 ^ dT) :=
  mast_le fun Y hY => card_le_of_cellsSmall _ dS dT rfl S T pS pT h Y hY

end Tree
end BalancedMast
