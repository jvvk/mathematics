import LeanProofs.NonNested.Short

/-!
# Lemma 4 of the note: the short stars fence in every other edge

If `G` has no strongly non-nested `3`-matching and contains the short stars at `a < b`
(`b - a ≥ 3`), then an edge `ij` with `j < b` avoiding `a` satisfies `i ≤ a - 2`, `j ≥ a + 2`
(`fence_L`), and an edge with `i > a` avoiding `b` satisfies `i ≤ b - 2`, `j ≥ b + 2`
(`fence_R`).

The proof is the note's: an edge separated from both `ij` and a star edge `σ` disjoint from `ij`
(the edge `(b, b+1)` for (L), `(a-1, a)` for (R)) forces `σ` to be nested with `ij`
(`nested_of_sep`). Deviation: the note obtains (R) from (L) by reversing the order; here (R) is
proved directly by the mirrored argument.
-/

set_option linter.style.longLine false

namespace NonNested

/-- If `g` is separated from two disjoint edges `e`, `f` of `G` and `G` has no strongly
non-nested `3`-matching, then `e` and `f` are nested. -/
theorem nested_of_sep {G : Finset Edge} (h : NoSNN 3 G) {e f g : Edge}
    (he : e ∈ G) (hf : f ∈ G) (hg : g ∈ G)
    (oe : e.1 < e.2) (of : f.1 < f.2) (og : g.1 < g.2)
    (hef : Disj e f) (seg : Separated e g) (sfg : Separated f g) : Nested e f := by
  by_contra hn
  obtain ⟨e1, e2⟩ := e; obtain ⟨f1, f2⟩ := f; obtain ⟨g1, g2⟩ := g
  simp only [Separated, Disj] at seg sfg hef oe of og
  exact h.not_fewCross he hf hg (by simp only [Disj]; omega) (by simp only [Disj]; omega)
    (by simp only [Disj]; omega) hn (by simp only [Nested]; omega) (by simp only [Nested]; omega)
    (by simp only [Crosses]; omega) (by simp only [Crosses]; omega) (by simp only [Crosses]; omega)

/-- `nested_of_sep` in the form used below: `¬ Disj e f ∨ Nested e f`. -/
theorem fence_aux {n : ℕ} {G : Finset Edge} (hG : IsGraph n G) (h : NoSNN 3 G) {e f g : Edge}
    (he : e ∈ G) (hf : f ∈ G) (hg : g ∈ G) (seg : Separated e g) (sfg : Separated f g) :
    ¬ Disj e f ∨ Nested e f := by
  by_cases hd : Disj e f
  · exact Or.inr (nested_of_sep h he hf hg (hG e he).2.1 (hG f hf).2.1 (hG g hg).2.1 hd seg sfg)
  · exact Or.inl hd

/-- **Lemma 4 (L).** -/
theorem fence_L {n : ℕ} {G : Finset Edge} (hG : IsGraph n G) (h : NoSNN 3 G) {a b : ℕ}
    (hab : a + 3 ≤ b) (hS : ShortStars G a b) {i j : ℕ} (hij : (i, j) ∈ G)
    (hj : j < b) (hia : i ≠ a) (hja : j ≠ a) : i ≤ a - 2 ∧ a + 2 ≤ j := by
  obtain ⟨s1, s2, s3, s4, -, -, s7, -⟩ := hS
  have o := hG _ hij; have o1 := hG _ s1; dsimp only at o o1
  have k1 := fence_aux hG h hij s1 s7 (by simp only [Separated]; omega) (by simp only [Separated]; omega)
  have k2 := fence_aux hG h hij s2 s7 (by simp only [Separated]; omega) (by simp only [Separated]; omega)
  have k3 := fence_aux hG h hij s3 s7 (by simp only [Separated]; omega) (by simp only [Separated]; omega)
  have k4 := fence_aux hG h hij s4 s7 (by simp only [Separated]; omega) (by simp only [Separated]; omega)
  simp only [Disj, Nested] at k1 k2 k3 k4
  omega

/-- **Lemma 4 (R).** -/
theorem fence_R {n : ℕ} {G : Finset Edge} (hG : IsGraph n G) (h : NoSNN 3 G) {a b : ℕ}
    (hab : a + 3 ≤ b) (hS : ShortStars G a b) {i j : ℕ} (hij : (i, j) ∈ G)
    (hi : a < i) (hib : i ≠ b) (hjb : j ≠ b) : i ≤ b - 2 ∧ b + 2 ≤ j := by
  obtain ⟨-, s2, -, -, t1, t2, t3, t4⟩ := hS
  have o := hG _ hij; have o2 := hG _ s2; dsimp only at o o2
  have k1 := fence_aux hG h hij t1 s2 (by simp only [Separated]; omega) (by simp only [Separated]; omega)
  have k2 := fence_aux hG h hij t2 s2 (by simp only [Separated]; omega) (by simp only [Separated]; omega)
  have k3 := fence_aux hG h hij t3 s2 (by simp only [Separated]; omega) (by simp only [Separated]; omega)
  have k4 := fence_aux hG h hij t4 s2 (by simp only [Separated]; omega) (by simp only [Separated]; omega)
  simp only [Disj, Nested] at k1 k2 k3 k4
  omega

end NonNested
