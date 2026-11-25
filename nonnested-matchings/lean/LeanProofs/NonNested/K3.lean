import LeanProofs.NonNested.Fence

/-!
# Theorem 1 of the note: `f₃(n) = f*₃(n) = 2n` for `n ≥ 6`

Upper bound (`f3_upper`), following Section 2 of the note. Let `G` have no strongly non-nested
`3`-matching and let `H = G ∪ S n`, where `S n` is the set of all `2n - 3` short edges. Short
edges lie in no crossing triple, so `H` has no three pairwise crossing edges (`noCross3_H`), and
Capoyleas–Pach gives `e(G) ≤ 2n - 7 + s` (`card_le_short`, the note's (2)), `s` the number of short
edges of `G`. By Lemma 3, `e(G) ≥ 2n + 1` forces `s = 8` (short stars at `a < b`) and
`e(H) = 4n - 10`. Pilaud–Santos at the chords `(a-1, a+1)` and `(b-1, b+1)`, with Lemma 4 ruling
out the wrong positions, produces three pairwise crossing edges `(x, b-1)`, `(y, b)`, `(a+1, v)`
of `G`: a contradiction.

Lower bound (`lowerGraph`): `K₅` on `{1, …, 5}` and every `v ≥ 6` joined to `1` and `2`; it has
`2n` edges and no non-nested `3`-matching (`noNN_lowerGraph`).

`theorem1` packages both: `2n` is the extremal number for `NoNN 3` and for `NoSNN 3`.
The two published theorems enter only as the hypotheses `CPHyp` and `PSHyp`.
-/

set_option linter.style.longLine false

namespace NonNested

/-! ### The short edges and the graph `H` -/

/-- All short edges on `[n]`: `(i, j)` with `1 ≤ i < j ≤ n` and `j - i ≤ 2`. -/
def S (n : ℕ) : Finset Edge :=
  ((Finset.Icc 1 n) ×ˢ (Finset.Icc 1 n)).filter (fun e => e.1 < e.2 ∧ e.2 ≤ e.1 + 2)

theorem mem_S {n : ℕ} {e : Edge} :
    e ∈ S n ↔ (1 ≤ e.1 ∧ e.1 ≤ n) ∧ (1 ≤ e.2 ∧ e.2 ≤ n) ∧ e.1 < e.2 ∧ e.2 ≤ e.1 + 2 := by
  simp [S, Finset.mem_product, Finset.mem_Icc, and_assoc]

theorem card_S {n : ℕ} (hn : 2 ≤ n) : (S n).card = 2 * n - 3 := by
  have hsplit : S n = (Finset.Ico 1 n).image (fun i => (i, i + 1)) ∪
      (Finset.Ico 1 (n - 1)).image (fun i => (i, i + 2)) := by
    ext ⟨x, y⟩
    rw [mem_S, Finset.mem_union, Finset.mem_image, Finset.mem_image]
    dsimp only
    constructor
    · intro h
      rcases (by omega : y = x + 1 ∨ y = x + 2) with rfl | rfl
      · exact Or.inl ⟨x, Finset.mem_Ico.2 (by omega), rfl⟩
      · exact Or.inr ⟨x, Finset.mem_Ico.2 (by omega), rfl⟩
    · rintro (⟨i, hi, he⟩ | ⟨i, hi, he⟩) <;> rw [Finset.mem_Ico] at hi <;>
        simp only [Prod.mk.injEq] at he <;> omega
  have hdisj : Disjoint ((Finset.Ico 1 n).image (fun i => (i, i + 1)))
      ((Finset.Ico 1 (n - 1)).image (fun i => (i, i + 2))) := by
    rw [Finset.disjoint_left]
    intro e h1 h2
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 h1
    obtain ⟨j, -, he⟩ := Finset.mem_image.1 h2
    simp only [Prod.mk.injEq] at he; omega
  have i1 : Function.Injective (fun i : ℕ => (i, i + 1)) := fun a b h => by
    simpa using congrArg Prod.fst h
  have i2 : Function.Injective (fun i : ℕ => (i, i + 2)) := fun a b h => by
    simpa using congrArg Prod.fst h
  rw [hsplit, Finset.card_union_of_disjoint hdisj, Finset.card_image_of_injective _ i1,
    Finset.card_image_of_injective _ i2, Nat.card_Ico, Nat.card_Ico]
  omega

/-- A short edge is never one of three pairwise crossing edges. -/
theorem cross3_short {e f g : Edge} (hef : Crosses e f) (hfg : Crosses f g) (heg : Crosses e g)
    (h : e.2 ≤ e.1 + 2 ∨ f.2 ≤ f.1 + 2 ∨ g.2 ≤ g.1 + 2) : False := by
  obtain ⟨e1, e2⟩ := e; obtain ⟨f1, f2⟩ := f; obtain ⟨g1, g2⟩ := g
  simp only [Crosses] at hef hfg heg h
  omega

theorem isGraph_H {n : ℕ} {G : Finset Edge} (hG : IsGraph n G) : IsGraph n (G ∪ S n) := by
  intro e he
  rcases Finset.mem_union.1 he with h | h
  · exact hG e h
  · have := mem_S.1 h; omega

/-- `H = G ∪ S n` has no three pairwise crossing edges. -/
theorem noCross3_H {n : ℕ} {G : Finset Edge} (h : NoSNN 3 G) : NoCross3 (G ∪ S n) := by
  intro e he f hf g hg hef hfg heg
  rcases Finset.mem_union.1 he with he | he
  · rcases Finset.mem_union.1 hf with hf | hf
    · rcases Finset.mem_union.1 hg with hg | hg
      · exact h.not_allCross he hf hg hef hfg heg
      · exact cross3_short hef hfg heg (Or.inr (Or.inr (mem_S.1 hg).2.2.2))
    · exact cross3_short hef hfg heg (Or.inr (Or.inl (mem_S.1 hf).2.2.2))
  · exact cross3_short hef hfg heg (Or.inl (mem_S.1 he).2.2.2)

theorem inter_S {n : ℕ} {G : Finset Edge} (hG : IsGraph n G) :
    G ∩ S n = G.filter (fun e => e.2 ≤ e.1 + 2) := by
  ext e
  rw [Finset.mem_inter, Finset.mem_filter, mem_S]
  constructor
  · rintro ⟨he, h⟩; exact ⟨he, h.2.2.2⟩
  · rintro ⟨he, h⟩; have := hG e he; exact ⟨he, by omega⟩

/-- The count: `e(G) + (2n - 3) = e(H) + s`. -/
theorem card_count {n : ℕ} (hn : 2 ≤ n) {G : Finset Edge} (hG : IsGraph n G) :
    G.card + (2 * n - 3) = (G ∪ S n).card + shortCount G := by
  have := Finset.card_union_add_card_inter G (S n)
  rw [inter_S hG, card_S hn] at this
  unfold shortCount; omega

/-- The note's (2): `e(G) ≤ 2n - 7 + s`. -/
theorem card_le_short (hCP : CPHyp) {n : ℕ} (hn : 5 ≤ n) {G : Finset Edge} (hG : IsGraph n G)
    (h : NoSNN 3 G) : G.card + 7 ≤ 2 * n + shortCount G := by
  have h1 := card_count (by omega) hG
  have h2 := hCP n (G ∪ S n) hn (isGraph_H hG) (noCross3_H h)
  omega

/-- A long edge of `H` (length at least `3`) is an edge of `G`. -/
theorem mem_G_of_long {n : ℕ} {G : Finset Edge} {e : Edge} (he : e ∈ G ∪ S n)
    (hl : e.1 + 3 ≤ e.2) : e ∈ G := by
  rcases Finset.mem_union.1 he with h | h
  · exact h
  · have := mem_S.1 h; omega

theorem edge_of_lt {x y : ℕ} (h : x < y) : edge x y = (x, y) := by
  simp [edge, min_eq_left h.le, max_eq_right h.le]

theorem edge_of_gt {x y : ℕ} (h : y < x) : edge x y = (y, x) := by
  simp [edge, min_eq_right h.le, max_eq_left h.le]

/-! ### The upper bound -/

/-- **Theorem 1, upper bound.** Given Capoyleas–Pach and Pilaud–Santos, an ordered graph on
`[n]`, `n ≥ 6`, with no strongly non-nested `3`-matching has at most `2n` edges. (Every graph
with no non-nested `3`-matching is such a graph, `noSNN_of_noNN`.) -/
theorem f3_upper (hCP : CPHyp) (hPS : PSHyp) {n : ℕ} (hn : 6 ≤ n) {G : Finset Edge}
    (hG : IsGraph n G) (h : NoSNN 3 G) : G.card ≤ 2 * n := by
  by_contra hc
  have hcount := card_count (by omega) hG
  have hCPH := hCP n (G ∪ S n) (by omega) (isGraph_H hG) (noCross3_H h)
  have h8le := short_le_eight hG h
  have h8 : shortCount G = 8 := by omega
  have hH : (G ∪ S n).card = 4 * n - 10 := by omega
  obtain ⟨a, b, ha, hab, hb, hS⟩ := short_eq_eight hG h h8
  have PS := hPS n (G ∪ S n) (by omega) (isGraph_H hG) (noCross3_H h) hH
  -- Pilaud–Santos at `a-1, a, a+1`: a long edge `(a+1, v)` of `G` with `v > b`.
  obtain ⟨p, rfl⟩ : ∃ p, a = p + 1 := ⟨a - 1, by omega⟩
  have hv : ∃ v, b < v ∧ (p + 2, v) ∈ G := by
    obtain ⟨u, v, cyc, -, -, c3, c4, -⟩ := PS p (by omega) (by omega)
    rcases cyc with ⟨hu, huv, hvn⟩ | ⟨-, -, -, hvp⟩ | ⟨-, -, hvp⟩
    · rw [edge_of_gt (by omega : p < u)] at c4
      have g4 := mem_G_of_long c4 (by dsimp only; omega)
      have hub : b ≤ u := by
        by_contra hub
        have := fence_L hG h hab hS g4 (by omega) (by omega) (by omega)
        omega
      rw [edge_of_lt (by omega : p + 2 < v)] at c3
      exact ⟨v, by omega, mem_G_of_long c3 (by dsimp only; omega)⟩
    all_goals
      rw [edge_of_gt (by omega : v < p + 2)] at c3
      have g3 := mem_G_of_long c3 (by dsimp only; omega)
      have := fence_L hG h hab hS g3 (by omega) (by omega) (by omega)
      omega
  obtain ⟨v, hbv, gv⟩ := hv
  -- Pilaud–Santos at `b-1, b, b+1`: long edges `(x, b-1)`, `(y, b)` of `G` with `x < y ≤ a`.
  obtain ⟨q, rfl⟩ : ∃ q, b = q + 1 := ⟨b - 1, by omega⟩
  obtain ⟨x, y, cyc, -, -, c3, c4, c5⟩ := PS q (by omega) (by omega)
  rcases cyc with ⟨hx, -, -⟩ | ⟨hx, -, -, -⟩ | ⟨hx, hxy, hyq⟩
  all_goals try
    rw [edge_of_gt (by omega : q < x)] at c4
    have g4 := mem_G_of_long c4 (by dsimp only; omega)
    have := fence_R hG h hab hS g4 (by omega) (by omega) (by omega)
    omega
  rw [edge_of_gt (by omega : y < q + 2)] at c3
  have g3 := mem_G_of_long c3 (by dsimp only; omega)
  have hya : y ≤ p + 1 := by
    by_contra hya
    have := fence_R hG h hab hS g3 (by omega) (by omega) (by omega)
    omega
  rw [edge_of_lt (by omega : x < q)] at c4
  rw [edge_of_lt (by omega : y < q + 1)] at c5
  have g4 := mem_G_of_long c4 (by dsimp only; omega)
  have g5 := mem_G_of_long c5 (by dsimp only; omega)
  -- `x < y < a+1 < b-1 < b < v`: three pairwise crossing edges of `G`.
  exact h.not_allCross g4 g5 gv (by simp only [Crosses]; omega) (by simp only [Crosses]; omega)
    (by simp only [Crosses]; omega)

/-! ### The lower bound -/

/-- The extremal graph: `K₅` on `{1, …, 5}` and every `v ≥ 6` joined to `1` and `2`. -/
def lowerGraph (n : ℕ) : Finset Edge :=
  ((Finset.Icc 1 n) ×ˢ (Finset.Icc 1 n)).filter (fun e => e.1 < e.2 ∧ (e.2 ≤ 5 ∨ e.1 ≤ 2))

theorem mem_lowerGraph {n : ℕ} {e : Edge} :
    e ∈ lowerGraph n ↔ (1 ≤ e.1 ∧ e.1 ≤ n) ∧ (1 ≤ e.2 ∧ e.2 ≤ n) ∧ e.1 < e.2 ∧ (e.2 ≤ 5 ∨ e.1 ≤ 2) := by
  simp [lowerGraph, Finset.mem_product, Finset.mem_Icc, and_assoc]

theorem isGraph_lowerGraph (n : ℕ) : IsGraph n (lowerGraph n) := by
  intro e he; have := mem_lowerGraph.1 he; omega

theorem card_lowerGraph {n : ℕ} (hn : 5 ≤ n) : (lowerGraph n).card = 2 * n := by
  induction n, hn using Nat.le_induction with
  | base => decide
  | succ m hm ih =>
    have hsplit : lowerGraph (m + 1) = insert (1, m + 1) (insert (2, m + 1) (lowerGraph m)) := by
      ext ⟨x, y⟩
      rw [Finset.mem_insert, Finset.mem_insert, mem_lowerGraph, mem_lowerGraph]
      simp only [Prod.mk.injEq]
      omega
    have n1 : (1, m + 1) ∉ insert (2, m + 1) (lowerGraph m) := by
      rw [Finset.mem_insert, mem_lowerGraph]; simp only [Prod.mk.injEq]; omega
    have n2 : (2, m + 1) ∉ lowerGraph m := by
      rw [mem_lowerGraph]; omega
    rw [hsplit, Finset.card_insert_of_notMem n1, Finset.card_insert_of_notMem n2, ih]
    ring

/-- The extremal graph has no non-nested `3`-matching: three disjoint edges need a vertex `≥ 6`;
the edge `g` reaching furthest right then has `g.1 ≤ 2`, and each other edge, ending before `g`
and not nested in it, starts before `g.1`; so both start at `1`. -/
theorem noNN_lowerGraph (n : ℕ) : NoNN 3 (lowerGraph n) := by
  intro M hM hc hNN
  obtain ⟨e, f, g, hef, heg, hfg, rfl⟩ := Finset.card_eq_three.1 hc
  have me := mem_lowerGraph.1 (hM (by simp : e ∈ ({e, f, g} : Finset Edge)))
  have mf := mem_lowerGraph.1 (hM (by simp : f ∈ ({e, f, g} : Finset Edge)))
  have mg := mem_lowerGraph.1 (hM (by simp : g ∈ ({e, f, g} : Finset Edge)))
  have pef := hNN e (by simp) f (by simp) hef
  have peg := hNN e (by simp) g (by simp) heg
  have pfg := hNN f (by simp) g (by simp) hfg
  obtain ⟨e1, e2⟩ := e; obtain ⟨f1, f2⟩ := f; obtain ⟨g1, g2⟩ := g
  simp only [Disj, Nested] at pef peg pfg me mf mg
  omega

/-- **Theorem 1.** For `n ≥ 6`, `f₃(n) = f*₃(n) = 2n`: `2n` is the extremal number both for
graphs with no non-nested `3`-matching and for graphs with no strongly non-nested
`3`-matching (given Capoyleas–Pach and Pilaud–Santos). -/
theorem theorem1 (hCP : CPHyp) (hPS : PSHyp) {n : ℕ} (hn : 6 ≤ n) :
    IsExtremal (NoNN 3) n (2 * n) ∧ IsExtremal (NoSNN 3) n (2 * n) := by
  have ex := card_lowerGraph (by omega : 5 ≤ n)
  refine ⟨⟨⟨lowerGraph n, isGraph_lowerGraph n, noNN_lowerGraph n, ex⟩, ?_⟩,
    ⟨⟨lowerGraph n, isGraph_lowerGraph n, noSNN_of_noNN (noNN_lowerGraph n), ex⟩, ?_⟩⟩
  · intro G hG hN; exact f3_upper hCP hPS hn hG (noSNN_of_noNN hN)
  · intro G hG hN; exact f3_upper hCP hPS hn hG hN

end NonNested
