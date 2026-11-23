import LeanProofs.Remoteness.Dist

/-!
# Caterpillars with legs

A spine path `0, 1, …, S` and `k` arms; arm `i` is a path of `ℓ i` new vertices hung at spine vertex `c i`. Every
tree in the note's headline has this form: a starlike tree (`S = 0`), a tree with two branch vertices (arms at `0`
and `S`), and the counterexample `T` (`S = 76`, arms at `0`, `53`, `76`).

Vertices: `inl s` (spine vertex `s`) and `inr ⟨i, j⟩` (the vertex at depth `j + 1` on arm `i`). We give the distance
in closed form and prove it is the graph distance with `dist_eq_of_local`.
-/

namespace Remoteness

/-- `|a - b|` on `ℕ`, in a form `omega` reads directly. -/
def ad (a b : ℕ) : ℕ := (a - b) + (b - a)

structure Cat where
  S : ℕ
  k : ℕ
  c : Fin k → ℕ
  ℓ : Fin k → ℕ
  hc : ∀ i, c i ≤ S

namespace Cat

variable (C : Cat)

abbrev V := Fin (C.S + 1) ⊕ (Σ i : Fin C.k, Fin (C.ℓ i))

/-- The generating relation: spine steps, arm roots, arm steps. -/
def rel : C.V → C.V → Prop
  | .inl s, .inl t => s.val + 1 = t.val
  | .inr ⟨i, j⟩, .inl s => j.val = 0 ∧ s.val = C.c i
  | .inr ⟨i, j⟩, .inr ⟨i', j'⟩ => i = i' ∧ j.val + 1 = j'.val
  | _, _ => False

def graph : SimpleGraph C.V := SimpleGraph.fromRel C.rel

/-- The closed-form distance. -/
def d : C.V → C.V → ℕ
  | .inl s, .inl t => ad s.val t.val
  | .inl s, .inr ⟨i, j⟩ => ad s.val (C.c i) + (j.val + 1)
  | .inr ⟨i, j⟩, .inl s => ad s.val (C.c i) + (j.val + 1)
  | .inr ⟨i, j⟩, .inr ⟨i', j'⟩ =>
      if i = i' then ad j.val j'.val else (j.val + 1) + ad (C.c i) (C.c i') + (j'.val + 1)

lemma d_self (v : C.V) : C.d v v = 0 := by
  rcases v with s | ⟨i, j⟩ <;> simp [d, ad]

lemma adj_iff (a b : C.V) : C.graph.Adj a b ↔ a ≠ b ∧ (C.rel a b ∨ C.rel b a) := by
  simp [graph, SimpleGraph.fromRel_adj]

/-- `d` changes by at most one along a generating step, in both directions. -/
lemma lip_rel (a b v : C.V) (h : C.rel a b) : C.d a v ≤ C.d b v + 1 ∧ C.d b v ≤ C.d a v + 1 := by
  rcases a with s | ⟨i, j⟩ <;> rcases b with t | ⟨i', j'⟩ <;> simp only [rel] at h
  · rcases v with u | ⟨i₂, j₂⟩ <;> simp only [d, ad] <;> omega
  · obtain ⟨hj, hs⟩ := h
    rcases v with u | ⟨i₂, j₂⟩
    · simp only [d, ad]; omega
    · simp only [d, ad]
      by_cases hi : i = i₂
      · subst hi; simp; omega
      · simp [hi]; omega
  · obtain ⟨hi, hj⟩ := h
    subst hi
    rcases v with u | ⟨i₂, j₂⟩
    · simp only [d, ad]; omega
    · simp only [d, ad]
      by_cases hi : i = i₂
      · subst hi; simp; omega
      · simp [hi]; omega

lemma lip (a b v : C.V) (h : C.graph.Adj a b) : C.d a v ≤ C.d b v + 1 := by
  rw [adj_iff] at h
  rcases h.2 with h | h
  · exact (C.lip_rel a b v h).1
  · exact (C.lip_rel b a v h).2

/-- One step from spine vertex `s` towards spine coordinate `t ≠ s`. -/
lemma spine_step (s : Fin (C.S + 1)) (t : ℕ) (ht : t ≤ C.S) (hne : s.val ≠ t) :
    ∃ s' : Fin (C.S + 1), C.graph.Adj (.inl s) (.inl s') ∧ ad s'.val t + 1 = ad s.val t := by
  rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
  · refine ⟨⟨s.val + 1, by omega⟩, ?_, ?_⟩
    · rw [adj_iff]; refine ⟨?_, Or.inl ?_⟩
      · intro h; simp [Fin.ext_iff] at h
      · simp [rel]
    · simp only [ad]; omega
  · refine ⟨⟨s.val - 1, by omega⟩, ?_, ?_⟩
    · rw [adj_iff]; refine ⟨?_, Or.inr ?_⟩
      · intro h; simp [Fin.ext_iff] at h; omega
      · simp [rel]; omega
    · simp only [ad]; omega

lemma step (u v : C.V) (hne : u ≠ v) : ∃ u', C.graph.Adj u u' ∧ C.d u' v + 1 = C.d u v := by
  rcases u with s | ⟨i, j⟩
  · rcases v with t | ⟨i', j'⟩
    · -- spine to spine
      have : s.val ≠ t.val := fun h => hne (by rw [Fin.ext h])
      obtain ⟨s', hadj, hd⟩ := C.spine_step s t.val (by omega) this
      exact ⟨.inl s', hadj, by simp only [d]; exact hd⟩
    · -- spine to arm `i'`: walk the spine to `c i'`, then step onto the arm
      by_cases hs : s.val = C.c i'
      · refine ⟨.inr ⟨i', ⟨0, by have := j'.isLt; omega⟩⟩, ?_, ?_⟩
        · rw [adj_iff]; refine ⟨by simp, Or.inr ?_⟩; simp [rel, hs]
        · simp only [d, ad]; simp; omega
      · obtain ⟨s', hadj, hd⟩ := C.spine_step s (C.c i') (C.hc i') hs
        exact ⟨.inl s', hadj, by simp only [d]; omega⟩
  · by_cases hsame : ∃ j', v = .inr ⟨i, j'⟩
    · -- same arm: move along the arm towards `j'`
      obtain ⟨j', rfl⟩ := hsame
      have hjj : j ≠ j' := fun h => hne (by rw [h])
      rcases Nat.lt_or_gt_of_ne (Fin.val_ne_of_ne hjj) with hlt | hgt
      · refine ⟨.inr ⟨i, ⟨j.val + 1, by omega⟩⟩, ?_, ?_⟩
        · rw [adj_iff]; refine ⟨?_, Or.inl ?_⟩
          · intro h; simp [Fin.ext_iff] at h
          · simp [rel]
        · simp only [d, ad]; simp; omega
      · refine ⟨.inr ⟨i, ⟨j.val - 1, by omega⟩⟩, ?_, ?_⟩
        · rw [adj_iff]; refine ⟨?_, Or.inr ?_⟩
          · intro h; simp [Fin.ext_iff] at h; omega
          · simp [rel]; omega
        · simp only [d, ad]; simp; omega
    · -- elsewhere: move towards the root of arm `i`
      push Not at hsame
      by_cases hj : j.val = 0
      · refine ⟨.inl ⟨C.c i, by have := C.hc i; omega⟩, ?_, ?_⟩
        · rw [adj_iff]; refine ⟨by simp, Or.inl ?_⟩; simp [rel, hj]
        · rcases v with t | ⟨i', j'⟩
          · simp only [d, ad]; omega
          · have hi : i ≠ i' := by
              intro h; subst h; exact hsame j' rfl
            simp only [d, ad, hi, if_false]; omega
      · refine ⟨.inr ⟨i, ⟨j.val - 1, by omega⟩⟩, ?_, ?_⟩
        · rw [adj_iff]; refine ⟨?_, Or.inr ?_⟩
          · intro h; simp [Fin.ext_iff] at h; omega
          · simp [rel]; omega
        · rcases v with t | ⟨i', j'⟩
          · simp only [d, ad]; omega
          · have hi : i ≠ i' := by
              intro h; subst h; exact hsame j' rfl
            simp only [d, ad, hi, if_false]; omega

/-- **The distance formula.** -/
theorem dist_eq (u v : C.V) : C.graph.dist u v = C.d u v :=
  dist_eq_of_local C.graph C.d C.d_self C.lip C.step u v

end Cat

end Remoteness
