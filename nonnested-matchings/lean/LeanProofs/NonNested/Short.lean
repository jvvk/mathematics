import LeanProofs.NonNested.Defs

/-!
# Lemma 3 of the note: the short edges

An edge is *short* if its length is `1` or `2`. In a graph with no strongly non-nested
`3`-matching there are at most `8` short edges (`short_le_eight`), and if there are exactly `8`
they form the *short stars* at two vertices `a < b` with `b - a ≥ 3` (`short_eq_eight`).

Deviation from the note, in the counting step only: the note bounds each length class by "a
union of paths with `m` edges has a matching of size `⌈m/2⌉`". Here the same bound (at most `4`
edges of each length) is obtained directly: among five edges of one length, listed by left end
`p₁ < ⋯ < p₅`, three are pairwise disjoint (`p₁, p₃, p₅` for length `1`; for length `2` one of
`p₁, p₃, p₅` / `p₁, p₂, p₅` / `p₁, p₄, p₅`). The classification of the equality case follows the
note: four unit edges with no `3`-matching are a path `t, …, t+4` or two two-edge paths centred
at `a < b`; the path case leaves five candidate length-`2` edges of which at most three can occur;
in the other case the length-`2` edges are among the four at `a` and `b` and the two chords
`(a-1, a+1)`, `(b-1, b+1)`, and either chord excludes both length-`2` edges at its own centre.
-/

set_option linter.style.longLine false

namespace NonNested

/-- Left ends of the length-`1` edges of `G`. -/
def P1 (G : Finset Edge) : Finset ℕ := (G.filter (fun e => e.2 = e.1 + 1)).image Prod.fst

/-- Left ends of the length-`2` edges of `G`. -/
def P2 (G : Finset Edge) : Finset ℕ := (G.filter (fun e => e.2 = e.1 + 2)).image Prod.fst

/-- The number of short edges (length at most `2`) of `G`. -/
def shortCount (G : Finset Edge) : ℕ := (G.filter (fun e => e.2 ≤ e.1 + 2)).card

theorem mem_P1 {G : Finset Edge} {p : ℕ} : p ∈ P1 G ↔ (p, p + 1) ∈ G := by
  constructor
  · intro h
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.1 h
    obtain ⟨he, h1⟩ := Finset.mem_filter.1 he
    rw [← h1]; exact he
  · intro h
    exact Finset.mem_image.2 ⟨(p, p + 1), Finset.mem_filter.2 ⟨h, rfl⟩, rfl⟩

theorem mem_P2 {G : Finset Edge} {p : ℕ} : p ∈ P2 G ↔ (p, p + 2) ∈ G := by
  constructor
  · intro h
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.1 h
    obtain ⟨he, h1⟩ := Finset.mem_filter.1 he
    rw [← h1]; exact he
  · intro h
    exact Finset.mem_image.2 ⟨(p, p + 2), Finset.mem_filter.2 ⟨h, rfl⟩, rfl⟩

/-- The short edges split by length: `s = |P1| + |P2|`. -/
theorem shortCount_eq {n : ℕ} {G : Finset Edge} (hG : IsGraph n G) :
    shortCount G = (P1 G).card + (P2 G).card := by
  have hsplit : G.filter (fun e => e.2 ≤ e.1 + 2) =
      G.filter (fun e => e.2 = e.1 + 1) ∪ G.filter (fun e => e.2 = e.1 + 2) := by
    ext e
    simp only [Finset.mem_filter, Finset.mem_union]
    constructor
    · rintro ⟨he, h⟩
      have := hG e he
      rcases (by omega : e.2 = e.1 + 1 ∨ e.2 = e.1 + 2) with h' | h'
      · exact Or.inl ⟨he, h'⟩
      · exact Or.inr ⟨he, h'⟩
    · rintro (⟨he, h⟩ | ⟨he, h⟩) <;> exact ⟨he, by omega⟩
  have hdisj : Disjoint (G.filter (fun e => e.2 = e.1 + 1)) (G.filter (fun e => e.2 = e.1 + 2)) := by
    rw [Finset.disjoint_filter]; intro e _ h; omega
  have inj : ∀ c : ℕ, Set.InjOn Prod.fst (↑(G.filter (fun e => e.2 = e.1 + c)) : Set Edge) := by
    intro c x hx y hy hxy
    have hx := (Finset.mem_filter.1 (Finset.mem_coe.1 hx)).2
    have hy := (Finset.mem_filter.1 (Finset.mem_coe.1 hy)).2
    exact Prod.ext hxy (by rw [hx, hy, hxy])
  unfold shortCount P1 P2
  rw [hsplit, Finset.card_union_of_disjoint hdisj, Finset.card_image_of_injOn (inj 1),
    Finset.card_image_of_injOn (inj 2)]

/-- Five elements of a finite set of naturals, listed in increasing order. -/
theorem exists_sorted5 {P : Finset ℕ} (h : 5 ≤ P.card) :
    ∃ p1 p2 p3 p4 p5 : ℕ, p1 ∈ P ∧ p2 ∈ P ∧ p3 ∈ P ∧ p4 ∈ P ∧ p5 ∈ P ∧
      p1 < p2 ∧ p2 < p3 ∧ p3 < p4 ∧ p4 < p5 := by
  obtain ⟨Q, hQ, hc⟩ := Finset.exists_subset_card_eq h
  have m := fun i => hQ (Q.orderEmbOfFin_mem hc i)
  have s := (Q.orderEmbOfFin hc).strictMono
  exact ⟨_, _, _, _, _, m 0, m 1, m 2, m 3, m 4, s (by decide), s (by decide), s (by decide),
    s (by decide)⟩

/-- The four elements of a four-element set of naturals, in increasing order. -/
theorem exists_sorted4 {P : Finset ℕ} (h : P.card = 4) :
    ∃ p1 p2 p3 p4 : ℕ, p1 ∈ P ∧ p2 ∈ P ∧ p3 ∈ P ∧ p4 ∈ P ∧ p1 < p2 ∧ p2 < p3 ∧ p3 < p4 := by
  have m := fun i => P.orderEmbOfFin_mem h i
  have s := (P.orderEmbOfFin h).strictMono
  exact ⟨_, _, _, _, m 0, m 1, m 2, m 3, s (by decide), s (by decide), s (by decide)⟩

/-- Three short edges of `G` (given by left end and length) are not pairwise disjoint: they
would form a strongly non-nested `3`-matching. -/
theorem NoSNN.noTri {G : Finset Edge} (h : NoSNN 3 G) {x y z l m k : ℕ}
    (hx : (x, x + l) ∈ G) (hy : (y, y + m) ∈ G) (hz : (z, z + k) ∈ G)
    (hl : 1 ≤ l ∧ l ≤ 2) (hm : 1 ≤ m ∧ m ≤ 2) (hk : 1 ≤ k ∧ k ≤ 2) :
    ¬ (Disj (x, x + l) (y, y + m) ∧ Disj (y, y + m) (z, z + k) ∧ Disj (x, x + l) (z, z + k)) :=
  fun ⟨a, b, c⟩ => h.not_shortTriple hx hy hz (by dsimp only; omega) (by dsimp only; omega)
    (by dsimp only; omega) a b c

/-- At most four edges of length `1`. -/
theorem card_P1_le {G : Finset Edge} (h : NoSNN 3 G) : (P1 G).card ≤ 4 := by
  by_contra hc
  obtain ⟨p1, p2, p3, p4, p5, h1, -, h3, -, h5, a, b, c, d⟩ := exists_sorted5 (P := P1 G) (by omega)
  have := h.noTri (mem_P1.1 h1) (mem_P1.1 h3) (mem_P1.1 h5) (by omega) (by omega) (by omega)
  simp only [Disj] at this; omega

/-- At most four edges of length `2`. -/
theorem card_P2_le {G : Finset Edge} (h : NoSNN 3 G) : (P2 G).card ≤ 4 := by
  by_contra hc
  obtain ⟨p1, p2, p3, p4, p5, h1, h2, h3, h4, h5, a, b, c, d⟩ := exists_sorted5 (P := P2 G) (by omega)
  have t135 := h.noTri (mem_P2.1 h1) (mem_P2.1 h3) (mem_P2.1 h5) (by omega) (by omega) (by omega)
  have t125 := h.noTri (mem_P2.1 h1) (mem_P2.1 h2) (mem_P2.1 h5) (by omega) (by omega) (by omega)
  have t145 := h.noTri (mem_P2.1 h1) (mem_P2.1 h4) (mem_P2.1 h5) (by omega) (by omega) (by omega)
  simp only [Disj] at t135 t125 t145; omega

/-- **Lemma 3, bound.** A graph with no strongly non-nested `3`-matching has at most `8` short
edges. -/
theorem short_le_eight {n : ℕ} {G : Finset Edge} (hG : IsGraph n G) (h : NoSNN 3 G) :
    shortCount G ≤ 8 := by
  rw [shortCount_eq hG]; have := card_P1_le h; have := card_P2_le h; omega

/-- The short stars at `a` and `b`: the eight edges of length at most `2` at `a` and at `b`. -/
def ShortStars (G : Finset Edge) (a b : ℕ) : Prop :=
  (a - 2, a) ∈ G ∧ (a - 1, a) ∈ G ∧ (a, a + 1) ∈ G ∧ (a, a + 2) ∈ G ∧
  (b - 2, b) ∈ G ∧ (b - 1, b) ∈ G ∧ (b, b + 1) ∈ G ∧ (b, b + 2) ∈ G

/-- If `P ⊆ s` misses two distinct elements `x, y` of `s`, then `|P| ≤ |s| - 2`. -/
theorem card_le_sub_two {P s : Finset ℕ} {x y : ℕ} (hP : P ⊆ s) (hx : x ∈ s) (hy : y ∈ s)
    (hxy : x ≠ y) (nx : x ∉ P) (ny : y ∉ P) : P.card ≤ s.card - 2 := by
  have hsub : P ⊆ (s.erase x).erase y := by
    intro q hq
    exact Finset.mem_erase.2 ⟨fun h => ny (h ▸ hq), Finset.mem_erase.2 ⟨fun h => nx (h ▸ hq), hP hq⟩⟩
  have := Finset.card_le_card hsub
  rw [Finset.card_erase_of_mem (Finset.mem_erase.2 ⟨hxy.symm, hy⟩), Finset.card_erase_of_mem hx] at this
  omega

/-- **Lemma 3, equality.** If a graph with no strongly non-nested `3`-matching has exactly `8`
short edges, they are the short stars at two vertices `a < b` with `b - a ≥ 3` (and then
`3 ≤ a`, `b + 2 ≤ n`). -/
theorem short_eq_eight {n : ℕ} {G : Finset Edge} (hG : IsGraph n G) (h : NoSNN 3 G)
    (h8 : shortCount G = 8) :
    ∃ a b : ℕ, 3 ≤ a ∧ a + 3 ≤ b ∧ b + 2 ≤ n ∧ ShortStars G a b := by
  rw [shortCount_eq hG] at h8
  have c1 := card_P1_le h
  have c2 := card_P2_le h
  have e1 : (P1 G).card = 4 := by omega
  have e2 : (P2 G).card = 4 := by omega
  obtain ⟨p1, p2, p3, p4, h1, h2, h3, h4, o12, o23, o34⟩ := exists_sorted4 e1
  have m1 := mem_P1.1 h1; have m2 := mem_P1.1 h2; have m3 := mem_P1.1 h3; have m4 := mem_P1.1 h4
  have g1 := hG _ m1
  -- Four unit edges with no `3`-matching: `p₂ = p₁ + 1` and `p₄ = p₃ + 1`.
  have t124 := h.noTri m1 m2 m4 (by omega) (by omega) (by omega)
  have t134 := h.noTri m1 m3 m4 (by omega) (by omega) (by omega)
  simp only [Disj] at t124 t134
  have q12 : p2 = p1 + 1 := by omega
  have q34 : p4 = p3 + 1 := by omega
  -- A length-`2` edge as the first of a triple with two unit edges.
  have tri : ∀ q ∈ P2 G, ∀ x ∈ P1 G, ∀ y ∈ P1 G,
      ¬ (Disj (q, q + 2) (x, x + 1) ∧ Disj (x, x + 1) (y, y + 1) ∧ Disj (q, q + 2) (y, y + 1)) :=
    fun q hq x hx y hy => h.noTri (mem_P2.1 hq) (mem_P1.1 hx) (mem_P1.1 hy) (by omega) (by omega) (by omega)
  -- Two length-`2` edges and a unit edge.
  have tri2 : ∀ q ∈ P2 G, ∀ r ∈ P2 G, ∀ x ∈ P1 G,
      ¬ (Disj (q, q + 2) (r, r + 2) ∧ Disj (r, r + 2) (x, x + 1) ∧ Disj (q, q + 2) (x, x + 1)) :=
    fun q hq r hr x hx => h.noTri (mem_P2.1 hq) (mem_P2.1 hr) (mem_P1.1 hx) (by omega) (by omega) (by omega)
  rcases Nat.lt_or_ge (p2 + 1) p3 with hgap | hgap
  · -- Two paths of two edges, centred at `a = p₂` and `b = p₄`.
    -- Every length-`2` edge is at `a` or `b`, or is one of the chords `(a-1,a+1)`, `(b-1,b+1)`.
    have loc : ∀ q ∈ P2 G, q + 2 = p2 ∨ q + 1 = p2 ∨ q = p2 ∨ q + 2 = p4 ∨ q + 1 = p4 ∨ q = p4 := by
      intro q hq
      have u13 := tri q hq p1 h1 p3 h3; have u14 := tri q hq p1 h1 p4 h4
      have u23 := tri q hq p2 h2 p3 h3; have u24 := tri q hq p2 h2 p4 h4
      simp only [Disj] at u13 u14 u23 u24; omega
    -- The chord `(a-1, a+1)` excludes both length-`2` edges at `a`; similarly at `b`.
    have chA : p1 ∈ P2 G → p2 - 2 ∉ P2 G ∧ p2 ∉ P2 G := by
      intro hc
      refine ⟨fun hq => ?_, fun hq => ?_⟩
      · have := tri2 p1 hc (p2 - 2) hq p4 h4; simp only [Disj] at this; omega
      · have := tri2 p1 hc p2 hq p4 h4; simp only [Disj] at this; omega
    have chB : p3 ∈ P2 G → p4 - 2 ∉ P2 G ∧ p4 ∉ P2 G := by
      intro hc
      refine ⟨fun hq => ?_, fun hq => ?_⟩
      · have := tri2 p3 hc (p4 - 2) hq p1 h1; simp only [Disj] at this; omega
      · have := tri2 p3 hc p4 hq p1 h1; simp only [Disj] at this; omega
    have nA : p1 ∉ P2 G := by
      intro hc
      obtain ⟨n1, n2⟩ := chA hc
      by_cases hb : p3 ∈ P2 G
      · obtain ⟨n3, n4⟩ := chB hb
        have hsub : P2 G ⊆ {p1, p3} := by
          intro q hq
          have := loc q hq
          have : q ≠ p2 - 2 := fun e => n1 (e ▸ hq)
          have : q ≠ p2 := fun e => n2 (e ▸ hq)
          have : q ≠ p4 - 2 := fun e => n3 (e ▸ hq)
          have : q ≠ p4 := fun e => n4 (e ▸ hq)
          simp only [Finset.mem_insert, Finset.mem_singleton]; omega
        have := (Finset.card_le_card hsub).trans Finset.card_le_two; omega
      · have hsub : P2 G ⊆ {p1, p4 - 2, p4} := by
          intro q hq
          have := loc q hq
          have : q ≠ p2 - 2 := fun e => n1 (e ▸ hq)
          have : q ≠ p2 := fun e => n2 (e ▸ hq)
          have : q ≠ p3 := fun e => hb (e ▸ hq)
          simp only [Finset.mem_insert, Finset.mem_singleton]; omega
        have := (Finset.card_le_card hsub).trans Finset.card_le_three; omega
    have nB : p3 ∉ P2 G := by
      intro hc
      obtain ⟨n3, n4⟩ := chB hc
      have hsub : P2 G ⊆ {p2 - 2, p2, p3} := by
        intro q hq
        have := loc q hq
        have : q ≠ p1 := fun e => nA (e ▸ hq)
        have : q ≠ p4 - 2 := fun e => n3 (e ▸ hq)
        have : q ≠ p4 := fun e => n4 (e ▸ hq)
        simp only [Finset.mem_insert, Finset.mem_singleton]; omega
      have := (Finset.card_le_card hsub).trans Finset.card_le_three; omega
    -- So the length-`2` edges are exactly the four at `a` and `b`.
    have hsub : P2 G ⊆ {p2 - 2, p2, p4 - 2, p4} := by
      intro q hq
      have := loc q hq
      have : q ≠ p1 := fun e => nA (e ▸ hq)
      have : q ≠ p3 := fun e => nB (e ▸ hq)
      simp only [Finset.mem_insert, Finset.mem_singleton]; omega
    have heq := Finset.eq_of_subset_of_card_le hsub (by rw [e2]; exact Finset.card_le_four)
    have k1 : p2 - 2 ∈ P2 G := by rw [heq]; simp
    have k2 : p2 ∈ P2 G := by rw [heq]; simp
    have k3 : p4 - 2 ∈ P2 G := by rw [heq]; simp
    have k4 : p4 ∈ P2 G := by rw [heq]; simp
    have r1 := mem_P2.1 k1; have r2 := mem_P2.1 k2; have r3 := mem_P2.1 k3; have r4 := mem_P2.1 k4
    have g2 := hG _ r1; have g4 := hG _ r4
    dsimp only at g2 g4
    refine ⟨p2, p4, by omega, by omega, by omega, ?_⟩
    have ea : p2 - 2 + 2 = p2 := by omega
    have eb : p4 - 2 + 2 = p4 := by omega
    have fa : p2 - 1 = p1 := by omega
    have fb : p4 - 1 = p3 := by omega
    rw [ea] at r1; rw [eb] at r3
    refine ⟨r1, ?_, m2, r2, r3, ?_, m4, r4⟩
    · rw [fa, q12] at *; exact m1
    · rw [fb, q34] at *; exact m3
  · -- One path `t, t+1, …, t+4` (`t = p₁`): impossible.
    exfalso
    have q23 : p3 = p2 + 1 := by omega
    -- Every length-`2` edge has left end in `[t-1, t+3]`.
    have loc : ∀ q ∈ P2 G, p1 ≤ q + 1 ∧ q ≤ p1 + 3 := by
      intro q hq
      have u13 := tri q hq p1 h1 p3 h3; have u14 := tri q hq p1 h1 p4 h4
      have u24 := tri q hq p2 h2 p4 h4
      simp only [Disj] at u13 u14 u24; omega
    -- `(t-1, t+1)` and `(t, t+2)` with `(t+3, t+4)`; `(t+3, t+5)` and `(t+2, t+4)` with `(t, t+1)`.
    have xA : p1 - 1 ∉ P2 G ∨ p1 ∉ P2 G := by
      by_contra hc; push Not at hc
      have := tri2 (p1 - 1) hc.1 p1 hc.2 p4 h4; simp only [Disj] at this; omega
    have xB : p1 + 3 ∉ P2 G ∨ p1 + 2 ∉ P2 G := by
      by_contra hc; push Not at hc
      have := tri2 (p1 + 3) hc.1 (p1 + 2) hc.2 p1 h1; simp only [Disj] at this; omega
    have hsub : P2 G ⊆ Finset.Icc (p1 - 1) (p1 + 3) := by
      intro q hq; have := loc q hq; rw [Finset.mem_Icc]; omega
    have hcard : (Finset.Icc (p1 - 1) (p1 + 3)).card = 5 := by rw [Nat.card_Icc]; omega
    have key : ∀ x y, x ∈ Finset.Icc (p1 - 1) (p1 + 3) → y ∈ Finset.Icc (p1 - 1) (p1 + 3) →
        x ≠ y → x ∉ P2 G → y ∉ P2 G → False := by
      intro x y hx hy hxy nx ny
      have := card_le_sub_two hsub hx hy hxy nx ny; omega
    rcases xA with nx | nx <;> rcases xB with ny | ny <;>
      exact key _ _ (by rw [Finset.mem_Icc]; omega) (by rw [Finset.mem_Icc]; omega) (by omega) nx ny

end NonNested
