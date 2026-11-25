import LeanProofs.NonNested.Defs

/-!
# Theorem 2 of the note: `f*₄(n) ≥ 3n + 1` for `n ≥ 9`

`G9` is the ordered graph on `[9]` with `A = {1, 2, 3}` independent, `B = {4, …, 9}` complete,
`N(1) = N(2) = {4, 7, 8, 9}`, `N(3) = {4, 6, 7, 8, 9}`; it has `28 = 3·9 + 1` edges (`card_G9`,
by evaluation of the explicit finite set). `noSNN4_G9` follows the note: list a non-nested
`4`-matching by left ends (`exists_sorted4_matching`; left and right ends are then in the same
order); with `t` edges inside `B`, `t ∈ {1, 2}`; for `t = 1` the edges are forced and
`(1,4) × (2,7)`, `(2,7) × (c,9)` with `(1,4)`, `(c,9)` separated; for `t = 2` the right end
`b₂` of the second edge is `6` or `7` and the first three edges give the pattern. In each case
crossing is not transitive on the matching.

`noSNN4_addVertex`: joining a new last vertex `n + 1` to `1, 2, 3` keeps the property, since a
non-nested matching through an edge `(i, n+1)` has all its left ends at most `i ≤ 3`.
`theorem2`: for every `n ≥ 9` a graph on `[n]` with `3n + 1` edges and no strongly non-nested
`4`-matching; `strong_conjecture_fails`: the strong form of Barát–Freschi–Tóth Conjecture 2.6
(`f*₄(n) ≤ 3n`) is false for every `n ≥ 9`.
-/

set_option linter.style.longLine false

namespace NonNested

/-- The graph `G9` on `[9]`. -/
def G9 : Finset Edge :=
  ((Finset.Icc 1 9) ×ˢ (Finset.Icc 1 9)).filter (fun e =>
    (4 ≤ e.1 ∧ e.1 < e.2) ∨
    ((e.1 = 1 ∨ e.1 = 2) ∧ (e.2 = 4 ∨ e.2 = 7 ∨ e.2 = 8 ∨ e.2 = 9)) ∨
    (e.1 = 3 ∧ (e.2 = 4 ∨ e.2 = 6 ∨ e.2 = 7 ∨ e.2 = 8 ∨ e.2 = 9)))

theorem mem_G9 {e : Edge} : e ∈ G9 ↔ (1 ≤ e.1 ∧ e.1 ≤ 9) ∧ (1 ≤ e.2 ∧ e.2 ≤ 9) ∧
    ((4 ≤ e.1 ∧ e.1 < e.2) ∨
    ((e.1 = 1 ∨ e.1 = 2) ∧ (e.2 = 4 ∨ e.2 = 7 ∨ e.2 = 8 ∨ e.2 = 9)) ∨
    (e.1 = 3 ∧ (e.2 = 4 ∨ e.2 = 6 ∨ e.2 = 7 ∨ e.2 = 8 ∨ e.2 = 9))) := by
  simp [G9, Finset.mem_product, Finset.mem_Icc, and_assoc]

/-- `G9` has `15 + 4 + 4 + 5 = 28` edges. -/
theorem card_G9 : G9.card = 28 := by decide

theorem isGraph_G9 : IsGraph 9 G9 := by
  intro e he; have := mem_G9.1 he; omega

/-- A non-nested `4`-matching listed by increasing left ends. -/
theorem exists_sorted4_matching {M : Finset Edge} (hc : M.card = 4) (hNN : IsNN M) :
    ∃ e1 e2 e3 e4 : Edge, e1 ∈ M ∧ e2 ∈ M ∧ e3 ∈ M ∧ e4 ∈ M ∧
      e1.1 < e2.1 ∧ e2.1 < e3.1 ∧ e3.1 < e4.1 := by
  have inj : Set.InjOn Prod.fst (↑M : Set Edge) := by
    intro e he f hf hef
    by_contra hne
    exact (hNN e he f hf hne).1.1 hef
  have hcard : (M.image Prod.fst).card = 4 := by rw [Finset.card_image_of_injOn inj, hc]
  have m := fun i => (M.image Prod.fst).orderEmbOfFin_mem hcard i
  have s := ((M.image Prod.fst).orderEmbOfFin hcard).strictMono
  obtain ⟨e1, h1, q1⟩ := Finset.mem_image.1 (m 0)
  obtain ⟨e2, h2, q2⟩ := Finset.mem_image.1 (m 1)
  obtain ⟨e3, h3, q3⟩ := Finset.mem_image.1 (m 2)
  obtain ⟨e4, h4, q4⟩ := Finset.mem_image.1 (m 3)
  refine ⟨e1, e2, e3, e4, h1, h2, h3, h4, ?_, ?_, ?_⟩
  · rw [q1, q2]; exact s (by decide)
  · rw [q2, q3]; exact s (by decide)
  · rw [q3, q4]; exact s (by decide)

/-- Pairs of a non-nested matching with distinct left ends. -/
theorem pair_of_lt {M : Finset Edge} (hNN : IsNN M) {e f : Edge} (he : e ∈ M) (hf : f ∈ M)
    (h : e.1 < f.1) : Disj e f ∧ ¬ Nested e f :=
  hNN e he f hf (fun hef => by rw [hef] at h; exact lt_irrefl _ h)

/-- **`G9` has no strongly non-nested `4`-matching.** -/
theorem noSNN4_G9 : NoSNN 4 G9 := by
  intro M hM hc hS
  obtain ⟨e1, e2, e3, e4, h1, h2, h3, h4, o12, o23, o34⟩ := exists_sorted4_matching hc hS.1
  have p12 := pair_of_lt hS.1 h1 h2 o12
  have p13 := pair_of_lt hS.1 h1 h3 (by omega)
  have p14 := pair_of_lt hS.1 h1 h4 (by omega)
  have p23 := pair_of_lt hS.1 h2 h3 o23
  have p24 := pair_of_lt hS.1 h2 h4 (by omega)
  have p34 := pair_of_lt hS.1 h3 h4 o34
  have g1 := mem_G9.1 (hM h1); have g2 := mem_G9.1 (hM h2)
  have g3 := mem_G9.1 (hM h3); have g4 := mem_G9.1 (hM h4)
  -- `e`, `f`, `g` of `M` with `e × f`, `f × g`, `e, g` separated contradict transitivity.
  have pattern : ∀ e ∈ M, ∀ f ∈ M, ∀ g ∈ M, Crosses e f → Crosses f g → Separated e g → False := by
    intro e he f hf g hg cef cfg seg
    have hne : e ≠ g := by
      rintro rfl; simp only [Separated] at seg; have := isGraph_G9 e (hM he); omega
    exact seg.not_crosses (hS.2 e he f hf g hg hne cef cfg)
  obtain ⟨l1, r1⟩ := e1; obtain ⟨l2, r2⟩ := e2; obtain ⟨l3, r3⟩ := e3; obtain ⟨l4, r4⟩ := e4
  simp only [Disj, Nested] at p12 p13 p14 p23 p24 p34 g1 g2 g3 g4 o12 o23 o34
  -- Left and right ends are in the same order.
  have r12 : r1 < r2 := by omega
  have r23 : r2 < r3 := by omega
  have r34 : r3 < r4 := by omega
  -- `t`, the number of edges inside `B`, is `1` or `2`.
  rcases Nat.lt_or_ge 3 l3 with ht | ht
  · rcases Nat.lt_or_ge 3 l2 with ht2 | ht2
    · -- `t ≥ 3`: seven distinct vertices of `B` would be used.
      omega
    · -- `t = 2`: `b₂ ∈ {6, 7}`.
      rcases (by omega : r2 = 7 ∨ r2 = 6) with hb | hb
      · -- `b₂ = 7`: `d₁ = 8`, `d₂ = 9`, `b₁ = 4`, `c₁ = 5`.
        have : r1 = 4 ∧ l3 = 5 ∧ r3 = 8 := by omega
        exact pattern _ h1 _ h2 _ h3 (by simp only [Crosses]; omega) (by simp only [Crosses]; omega)
          (by simp only [Separated]; omega)
      · -- `b₂ = 6`: `a₂ = 3`, `b₁ = 4`, `c₁ = 5`.
        have : l2 = 3 ∧ r1 = 4 ∧ l3 = 5 := by omega
        exact pattern _ h1 _ h2 _ h3 (by simp only [Crosses]; omega) (by simp only [Crosses]; omega)
          (by simp only [Separated]; omega)
  · rcases Nat.lt_or_ge 3 l4 with ht4 | ht4
    · -- `t = 1`: the edges are `(1,4)`, `(2,7)`, `(3,8)`, `(c,9)` with `c ∈ {5, 6}`.
      have : l1 = 1 ∧ l2 = 2 ∧ l3 = 3 ∧ r1 = 4 ∧ r2 = 7 ∧ r3 = 8 ∧ r4 = 9 ∧ (l4 = 5 ∨ l4 = 6) := by
        omega
      exact pattern _ h1 _ h2 _ h4 (by simp only [Crosses]; omega) (by simp only [Crosses]; omega)
        (by simp only [Separated]; omega)
    · -- `t = 0`: four distinct left ends in `A`.
      omega

/-- Join a new last vertex `n + 1` to `1`, `2`, `3`. -/
def addVertex (n : ℕ) (G : Finset Edge) : Finset Edge :=
  G ∪ {(1, n + 1), (2, n + 1), (3, n + 1)}

theorem isGraph_addVertex {n : ℕ} {G : Finset Edge} (hn : 3 ≤ n) (hG : IsGraph n G) :
    IsGraph (n + 1) (addVertex n G) := by
  intro e he
  rcases Finset.mem_union.1 he with h | h
  · have := hG e h; omega
  · simp only [Finset.mem_insert, Finset.mem_singleton] at h
    rcases h with rfl | rfl | rfl <;> dsimp only <;> omega

theorem card_addVertex {n : ℕ} {G : Finset Edge} (hG : IsGraph n G) :
    (addVertex n G).card = G.card + 3 := by
  have hd : Disjoint G {(1, n + 1), (2, n + 1), (3, n + 1)} := by
    rw [Finset.disjoint_right]
    intro e he hG'
    have := hG e hG'
    simp only [Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl | rfl <;> dsimp only at this <;> omega
  unfold addVertex
  rw [Finset.card_union_of_disjoint hd, card_triple (by simp) (by simp) (by simp)]

/-- Adding the vertex keeps the graph free of strongly non-nested `4`-matchings: a non-nested
matching using an edge `(i, n+1)`, `i ≤ 3`, has all its left ends at most `i` (as `n + 1` is the
last right end), so it has at most three edges. -/
theorem noSNN4_addVertex {n : ℕ} {G : Finset Edge} (hn : 3 ≤ n) (hG : IsGraph n G)
    (h : NoSNN 4 G) : NoSNN 4 (addVertex n G) := by
  intro M hM hc hS
  by_cases hsub : M ⊆ G
  · exact h M hsub hc hS
  obtain ⟨e, he, heG⟩ := Finset.not_subset.1 hsub
  have hnew : e ∈ ({(1, n + 1), (2, n + 1), (3, n + 1)} : Finset Edge) := by
    rcases Finset.mem_union.1 (hM he) with h' | h'
    · exact absurd h' heG
    · exact h'
  have hG' := isGraph_addVertex hn hG
  have hi : e.1 ≤ 3 ∧ e.2 = n + 1 := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hnew
    rcases hnew with rfl | rfl | rfl <;> dsimp only <;> omega
  -- Every left end of `M` lies in `[1, 3]`.
  have hsub3 : M.image Prod.fst ⊆ Finset.Icc 1 3 := by
    intro x hx
    obtain ⟨f, hf, rfl⟩ := Finset.mem_image.1 hx
    have gf := hG' f (hM hf)
    rw [Finset.mem_Icc]
    by_cases hfe : f = e
    · subst hfe; omega
    · obtain ⟨hd, hnn⟩ := hS.1 f hf e he hfe
      obtain ⟨f1, f2⟩ := f; obtain ⟨e1, e2⟩ := e
      simp only [Disj, Nested] at hd hnn gf hi ⊢
      omega
  have inj : Set.InjOn Prod.fst (↑M : Set Edge) := by
    intro x hx y hy hxy
    by_contra hne
    exact (hS.1 x hx y hy hne).1.1 hxy
  have := Finset.card_le_card hsub3
  rw [Finset.card_image_of_injOn inj, hc, Nat.card_Icc] at this
  omega

/-- **Theorem 2.** For every `n ≥ 9` there is an ordered graph on `[n]` with `3n + 1` edges and
no strongly non-nested `4`-matching: `f*₄(n) ≥ 3n + 1`. -/
theorem theorem2 {n : ℕ} (hn : 9 ≤ n) :
    ∃ G : Finset Edge, IsGraph n G ∧ NoSNN 4 G ∧ G.card = 3 * n + 1 := by
  induction n, hn using Nat.le_induction with
  | base => exact ⟨G9, isGraph_G9, noSNN4_G9, card_G9⟩
  | succ m hm ih =>
    obtain ⟨G, hG, hN, hc⟩ := ih
    exact ⟨addVertex m G, isGraph_addVertex (by omega) hG, noSNN4_addVertex (by omega) hG hN,
      by rw [card_addVertex hG, hc]; ring⟩

/-- The strong form of Barát–Freschi–Tóth Conjecture 2.6 fails for `k = 4`: for every `n ≥ 9`
it is not true that every graph on `[n]` with no strongly non-nested `4`-matching has at most
`3n` edges. -/
theorem strong_conjecture_fails {n : ℕ} (hn : 9 ≤ n) :
    ¬ ∀ G : Finset Edge, IsGraph n G → NoSNN 4 G → G.card ≤ 3 * n := by
  intro hall
  obtain ⟨G, hG, hN, hc⟩ := theorem2 hn
  have := hall G hG hN
  omega

end NonNested
