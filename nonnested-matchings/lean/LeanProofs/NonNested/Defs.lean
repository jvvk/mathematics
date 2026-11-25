import Mathlib

/-!
# Non-nested matchings in ordered graphs: definitions

Notation follows `nonnested.tex` (the note proving the case `k = 3` of Barát, Freschi and Tóth,
Conjecture 2.6, and disproving its strong form for `k = 4`).

An ordered graph on `[n] = {1, …, n}` is a finite set `G` of pairs `(i, j)` with `1 ≤ i < j ≤ n`
(`IsGraph n G`). For disjoint edges `ij`, `st` the three relations `Nested`, `Crosses`,
`Separated` are those of the note; all three are symmetric. A set `M` of edges is a non-nested
matching (`IsNN M`) if its edges are pairwise disjoint and pairwise non-nested, and strongly
non-nested (`IsSNN M`) if in addition crossing is transitive on it (so an equivalence relation,
crossing being symmetric). `NoNN k G` and `NoSNN k G` say that `G` has no such matching with `k`
edges.

The two published theorems the note uses enter as hypotheses: `CPHyp` (Capoyleas and Pach) and
`PSHyp` (Pilaud and Santos).
-/

set_option linter.style.longLine false

namespace NonNested

/-- An edge `(i, j)`, written with `i < j`. -/
abbrev Edge := ℕ × ℕ

/-- `G` is an ordered graph on `[n]`: every edge `(i, j)` has `1 ≤ i < j ≤ n`. -/
def IsGraph (n : ℕ) (G : Finset Edge) : Prop :=
  ∀ e ∈ G, 1 ≤ e.1 ∧ e.1 < e.2 ∧ e.2 ≤ n

/-- Two edges are disjoint: no common endpoint. -/
def Disj (e f : Edge) : Prop :=
  e.1 ≠ f.1 ∧ e.1 ≠ f.2 ∧ e.2 ≠ f.1 ∧ e.2 ≠ f.2

/-- One edge lies strictly inside the other. -/
def Nested (e f : Edge) : Prop :=
  (e.1 < f.1 ∧ f.2 < e.2) ∨ (f.1 < e.1 ∧ e.2 < f.2)

/-- The two edges cross: `i < s < j < t` or `s < i < t < j`. -/
def Crosses (e f : Edge) : Prop :=
  (e.1 < f.1 ∧ f.1 < e.2 ∧ e.2 < f.2) ∨ (f.1 < e.1 ∧ e.1 < f.2 ∧ f.2 < e.2)

/-- The two edges are separated: one ends before the other starts. -/
def Separated (e f : Edge) : Prop :=
  e.2 < f.1 ∨ f.2 < e.1

/-- A non-nested matching: pairwise disjoint, pairwise non-nested edges. -/
def IsNN (M : Finset Edge) : Prop :=
  ∀ e ∈ M, ∀ f ∈ M, e ≠ f → Disj e f ∧ ¬ Nested e f

/-- A strongly non-nested matching: non-nested, and crossing is transitive on it. Since crossing
is symmetric, this makes "equal or crossing" an equivalence relation: the matching splits into
blocks of pairwise crossing edges, and edges of different blocks are separated. -/
def IsSNN (M : Finset Edge) : Prop :=
  IsNN M ∧ ∀ e ∈ M, ∀ f ∈ M, ∀ g ∈ M, e ≠ g → Crosses e f → Crosses f g → Crosses e g

/-- `G` contains no non-nested matching with `k` edges. -/
def NoNN (k : ℕ) (G : Finset Edge) : Prop :=
  ∀ M ⊆ G, M.card = k → ¬ IsNN M

/-- `G` contains no strongly non-nested matching with `k` edges. -/
def NoSNN (k : ℕ) (G : Finset Edge) : Prop :=
  ∀ M ⊆ G, M.card = k → ¬ IsSNN M

/-- `H` has no three pairwise crossing edges. -/
def NoCross3 (H : Finset Edge) : Prop :=
  ∀ e ∈ H, ∀ f ∈ H, ∀ g ∈ H, Crosses e f → Crosses f g → Crosses e g → False

/-- The edge joining `x` and `y`, normalised as `(min, max)`. -/
def edge (x y : ℕ) : Edge := (min x y, max x y)

/-- `p, p+1, p+2, u, v` are in cyclic order on `[1, n]` (and are five distinct vertices). -/
def CycOrder5 (n p u v : ℕ) : Prop :=
  (p + 2 < u ∧ u < v ∧ v ≤ n) ∨ (p + 2 < u ∧ u ≤ n ∧ 1 ≤ v ∧ v < p) ∨ (1 ≤ u ∧ u < v ∧ v < p)

/-- **Capoyleas–Pach** (J. Combin. Theory Ser. B 56 (1992) 9–15), case `k = 2` of their theorem:
a set of chords of a convex `n`-gon, `n ≥ 5`, with no three pairwise crossing chords has at most
`4n - 10` chords. Placing `[n]` on a circle in its natural order turns `Crosses` into crossing of
chords, so this is the statement for ordered graphs. Used as a hypothesis, not proved. -/
def CPHyp : Prop :=
  ∀ (n : ℕ) (H : Finset Edge), 5 ≤ n → IsGraph n H → NoCross3 H → H.card ≤ 4 * n - 10

/-- **Pilaud–Santos**, *Multitriangulations as complexes of star polygons*, Discrete Comput.
Geom. 41 (2009) 284–317, Corollary 4.2(ii), case `k = 2`: in a `2`-triangulation of the `n`-gon
(a maximal set of chords with no three pairwise crossing), every `2`-boundary edge (a chord
joining two vertices at cyclic distance `2`) belongs to exactly one `2`-star, which lies on the
side of the chord containing the single vertex between its ends.

Stated, as in the note, for the chords `{p, p+2}` with `1 ≤ p`, `p + 2 ≤ n` (only existence is
used): the star has vertices `p, p+1, p+2, u, v` in cyclic order and its five chords
`{p,p+2}, {p+1,u}, {p+2,v}, {u,p}, {v,p+1}` lie in `H`. A `2`-triangulation is described as a
graph with no three pairwise crossing edges and `4n - 10` edges; by `CPHyp` such a graph is
maximal, so this is implied by the published corollary together with Capoyleas–Pach. Used as a
hypothesis, not proved. -/
def PSHyp : Prop :=
  ∀ (n : ℕ) (H : Finset Edge), 5 ≤ n → IsGraph n H → NoCross3 H → H.card = 4 * n - 10 →
    ∀ p : ℕ, 1 ≤ p → p + 2 ≤ n → ∃ u v : ℕ, CycOrder5 n p u v ∧
      edge p (p + 2) ∈ H ∧ edge (p + 1) u ∈ H ∧ edge (p + 2) v ∈ H ∧
      edge u p ∈ H ∧ edge v (p + 1) ∈ H

/-- `m` is the extremal number for the property `P` on `[n]`: some graph on `[n]` with `P` has
`m` edges, and every graph on `[n]` with `P` has at most `m`. With `P = NoNN k` this says
`f_k(n) = m`, with `P = NoSNN k` it says `f*_k(n) = m`. -/
def IsExtremal (P : Finset Edge → Prop) (n m : ℕ) : Prop :=
  (∃ G, IsGraph n G ∧ P G ∧ G.card = m) ∧ ∀ G, IsGraph n G → P G → G.card ≤ m

/-! ### Basic facts -/

theorem Disj.ne {e f : Edge} (h : Disj e f) : e ≠ f := by
  rintro rfl; exact h.1 rfl

/-- Every strongly non-nested matching is non-nested, so `NoNN k G → NoSNN k G`. -/
theorem noSNN_of_noNN {k : ℕ} {G : Finset Edge} (h : NoNN k G) : NoSNN k G :=
  fun M hM hc hS => h M hM hc hS.1

theorem crosses_symm {e f : Edge} (h : Crosses e f) : Crosses f e := by
  unfold Crosses at *; omega

theorem Crosses.disj {e f : Edge} (h : Crosses e f) : Disj e f := by
  unfold Crosses Disj at *; omega

theorem Crosses.not_nested {e f : Edge} (h : Crosses e f) : ¬ Nested e f := by
  unfold Crosses Nested at *; omega

theorem Separated.not_crosses {e f : Edge} (h : Separated e f) : ¬ Crosses e f := by
  unfold Crosses Separated at *; omega

theorem card_triple {e f g : Edge} (hef : e ≠ f) (hfg : f ≠ g) (heg : e ≠ g) :
    ({e, f, g} : Finset Edge).card = 3 :=
  Finset.card_eq_three.2 ⟨e, f, g, hef, heg, hfg, rfl⟩

/-- Three pairwise disjoint, pairwise non-nested edges in which no edge crosses both others form
a strongly non-nested matching (crossing is then vacuously transitive). -/
theorem isSNN_of_fewCross {e f g : Edge}
    (hef : Disj e f) (hfg : Disj f g) (heg : Disj e g)
    (nef : ¬ Nested e f) (nfg : ¬ Nested f g) (neg : ¬ Nested e g)
    (ce : ¬ (Crosses e f ∧ Crosses e g)) (cf : ¬ (Crosses f e ∧ Crosses f g))
    (cg : ¬ (Crosses g e ∧ Crosses g f)) : IsSNN {e, f, g} := by
  have sym : ∀ x y : Edge, Disj x y → Disj y x := by
    intro x y h; unfold Disj at *; omega
  have nsym : ∀ x y : Edge, ¬ Nested x y → ¬ Nested y x := by
    intro x y h; unfold Nested at *; omega
  refine ⟨?_, ?_⟩
  · intro x hx y hy hxy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
    rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;>
      first
      | exact absurd rfl hxy
      | exact ⟨hef, nef⟩ | exact ⟨hfg, nfg⟩ | exact ⟨heg, neg⟩
      | exact ⟨sym _ _ hef, nsym _ _ nef⟩ | exact ⟨sym _ _ hfg, nsym _ _ nfg⟩
      | exact ⟨sym _ _ heg, nsym _ _ neg⟩
  · intro x hx y hy z hz hxz hxy hyz
    exfalso
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy hz
    rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;>
      rcases hz with rfl | rfl | rfl <;>
      first
      | exact absurd rfl hxz
      | exact (hxy.disj.1 rfl).elim
      | exact (hyz.disj.1 rfl).elim
      | exact ce ⟨crosses_symm hxy, hyz⟩ | exact cf ⟨crosses_symm hxy, hyz⟩
      | exact cg ⟨crosses_symm hxy, hyz⟩
      | exact ce ⟨hyz, crosses_symm hxy⟩ | exact cf ⟨hyz, crosses_symm hxy⟩
      | exact cg ⟨hyz, crosses_symm hxy⟩

/-- Three pairwise crossing edges form a strongly non-nested matching. -/
theorem isSNN_of_allCross {e f g : Edge} (hef : Crosses e f) (hfg : Crosses f g)
    (heg : Crosses e g) : IsSNN {e, f, g} := by
  refine ⟨?_, ?_⟩
  · intro x hx y hy hxy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
    rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;>
      first
      | exact absurd rfl hxy
      | exact ⟨hef.disj, hef.not_nested⟩ | exact ⟨hfg.disj, hfg.not_nested⟩
      | exact ⟨heg.disj, heg.not_nested⟩
      | exact ⟨(crosses_symm hef).disj, (crosses_symm hef).not_nested⟩
      | exact ⟨(crosses_symm hfg).disj, (crosses_symm hfg).not_nested⟩
      | exact ⟨(crosses_symm heg).disj, (crosses_symm heg).not_nested⟩
  · intro x hx y hy z hz hxz _ _
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx hz
    rcases hx with rfl | rfl | rfl <;> rcases hz with rfl | rfl | rfl <;>
      first
      | exact absurd rfl hxz
      | exact hef | exact hfg | exact heg
      | exact crosses_symm hef | exact crosses_symm hfg | exact crosses_symm heg

/-- In a graph with no strongly non-nested `3`-matching, a triple as in `isSNN_of_fewCross`
cannot occur. -/
theorem NoSNN.not_fewCross {G : Finset Edge} (h : NoSNN 3 G) {e f g : Edge}
    (he : e ∈ G) (hf : f ∈ G) (hg : g ∈ G)
    (hef : Disj e f) (hfg : Disj f g) (heg : Disj e g)
    (nef : ¬ Nested e f) (nfg : ¬ Nested f g) (neg : ¬ Nested e g)
    (ce : ¬ (Crosses e f ∧ Crosses e g)) (cf : ¬ (Crosses f e ∧ Crosses f g))
    (cg : ¬ (Crosses g e ∧ Crosses g f)) : False := by
  refine h {e, f, g} ?_ (card_triple hef.ne hfg.ne heg.ne)
    (isSNN_of_fewCross hef hfg heg nef nfg neg ce cf cg)
  intro x hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl | rfl <;> assumption

/-- In a graph with no strongly non-nested `3`-matching there are no three pairwise crossing
edges. -/
theorem NoSNN.not_allCross {G : Finset Edge} (h : NoSNN 3 G) {e f g : Edge}
    (he : e ∈ G) (hf : f ∈ G) (hg : g ∈ G)
    (hef : Crosses e f) (hfg : Crosses f g) (heg : Crosses e g) : False := by
  refine h {e, f, g} ?_ (card_triple hef.disj.ne hfg.disj.ne heg.disj.ne)
    (isSNN_of_allCross hef hfg heg)
  intro x hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl | rfl <;> assumption

/-- A short edge (length at most `2`) together with two disjoint short edges forms no nested
pair and each crosses at most one of the others: three pairwise disjoint edges of length at
most `2` in a graph with no strongly non-nested `3`-matching cannot occur. -/
theorem NoSNN.not_shortTriple {G : Finset Edge} (h : NoSNN 3 G) {e f g : Edge}
    (he : e ∈ G) (hf : f ∈ G) (hg : g ∈ G)
    (le : e.1 < e.2 ∧ e.2 ≤ e.1 + 2) (lf : f.1 < f.2 ∧ f.2 ≤ f.1 + 2)
    (lg : g.1 < g.2 ∧ g.2 ≤ g.1 + 2)
    (hef : Disj e f) (hfg : Disj f g) (heg : Disj e g) : False := by
  obtain ⟨e1, e2⟩ := e; obtain ⟨f1, f2⟩ := f; obtain ⟨g1, g2⟩ := g
  simp only [Disj] at hef hfg heg le lf lg
  exact h.not_fewCross he hf hg (by simp only [Disj]; omega) (by simp only [Disj]; omega)
    (by simp only [Disj]; omega) (by simp only [Nested]; omega) (by simp only [Nested]; omega)
    (by simp only [Nested]; omega) (by simp only [Crosses]; omega)
    (by simp only [Crosses]; omega) (by simp only [Crosses]; omega)

end NonNested
