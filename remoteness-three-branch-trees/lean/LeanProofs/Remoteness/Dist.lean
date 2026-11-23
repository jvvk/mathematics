import Mathlib

/-!
# Recognising the graph distance

If `d` vanishes on the diagonal, changes by at most one along every edge, and every vertex `u ≠ v` has a
neighbour one step closer to `v`, then `d` is the graph distance. This lets us compute distances in the explicit
trees of the note from closed formulas.
-/

namespace Remoteness

open SimpleGraph

variable {V : Type*} (G : SimpleGraph V) (d : V → V → ℕ)

/-- A walk from `u` to `v` has length at least `d u v` when `d` is 1-Lipschitz along edges and `d v v = 0`. -/
lemma le_length_of_lipschitz (h0 : ∀ v, d v v = 0) (hlip : ∀ a b v, G.Adj a b → d a v ≤ d b v + 1) :
    ∀ {u v : V} (p : G.Walk u v), d u v ≤ p.length := by
  intro u v p
  induction p with
  | nil => simp [h0]
  | @cons a b w hadj p ih => simp only [Walk.length_cons]; have := hlip a b w hadj; omega

/-- With a step towards `v` from every `u ≠ v`, there is a walk of length `d u v`. -/
lemma exists_walk_of_step (h0 : ∀ v, d v v = 0)
    (hstep : ∀ u v, u ≠ v → ∃ u', G.Adj u u' ∧ d u' v + 1 = d u v) :
    ∀ (n : ℕ) (u v : V), d u v = n → ∃ p : G.Walk u v, p.length = n := by
  intro n
  induction n with
  | zero =>
    intro u v h
    by_cases huv : u = v
    · subst huv; exact ⟨Walk.nil, rfl⟩
    · obtain ⟨u', -, hu'⟩ := hstep u v huv; omega
  | succ n ih =>
    intro u v h
    by_cases huv : u = v
    · subst huv; rw [h0] at h; omega
    · obtain ⟨u', hadj, hu'⟩ := hstep u v huv
      obtain ⟨p, hp⟩ := ih u' v (by omega)
      exact ⟨Walk.cons hadj p, by simp [hp]⟩

/-- **Distance recognition.** -/
theorem dist_eq_of_local (h0 : ∀ v, d v v = 0) (hlip : ∀ a b v, G.Adj a b → d a v ≤ d b v + 1)
    (hstep : ∀ u v, u ≠ v → ∃ u', G.Adj u u' ∧ d u' v + 1 = d u v) (u v : V) :
    G.dist u v = d u v := by
  obtain ⟨p, hp⟩ := exists_walk_of_step G d h0 hstep (d u v) u v rfl
  apply le_antisymm
  · exact hp ▸ dist_le p
  · obtain ⟨q, hq⟩ := Reachable.exists_walk_length_eq_dist (G := G) ⟨p⟩
    rw [← hq]; exact le_length_of_lipschitz G d h0 hlip q

/-- Under the same hypotheses the graph is connected. -/
theorem connected_of_local [Nonempty V] (h0 : ∀ v, d v v = 0)
    (hstep : ∀ u v, u ≠ v → ∃ u', G.Adj u u' ∧ d u' v + 1 = d u v) : G.Connected := by
  refine ⟨fun u v => ?_⟩
  obtain ⟨p, -⟩ := exists_walk_of_step G d h0 hstep (d u v) u v rfl
  exact ⟨p⟩

end Remoteness
