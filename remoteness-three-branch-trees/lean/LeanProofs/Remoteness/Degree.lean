import LeanProofs.Remoteness.Headline

/-!
# Degrees and branch vertices of caterpillars

From the distance formula `Cat.dist_eq`, two vertices are adjacent exactly when the closed-form distance is `1`, so
degrees are counts of a closed formula:

* a spine vertex `s` has degree `[0 < s] + [s < S] + #{arms rooted at s}`;
* a vertex on an arm has degree `1 + [it is not the arm's end]`, so at most `2`.

Consequences, as graphs: `T` has exactly three branch vertices (spine `0`, `53`, `76`); a starlike caterpillar has
exactly one; a `TwoHub` caterpillar has exactly two (the ends of its spine). So the classes compared in `headline`
are the trees with one and with two branch vertices among caterpillars, and `T` has three.
-/

namespace Remoteness

open Finset SimpleGraph Cat

namespace Cat

variable (C : Cat)

open Classical in
/-- Branch vertices: degree at least `3`. -/
noncomputable def branch : Finset C.V := univ.filter (fun v => 3 ≤ C.graph.degree v)

lemma cnt (n : ℕ) (p : ℕ → Prop) [DecidablePred p] :
    (∑ t : Fin n, if p t.val then 1 else 0) = #((range n).filter p) := by
  rw [Fin.sum_univ_eq_sum_range (fun t => if p t then 1 else 0), Finset.card_filter]

lemma cnt_ad (n a : ℕ) (ha : a < n) :
    #((range n).filter (fun t => ad a t = 1)) = (if 0 < a then 1 else 0) + (if a + 1 < n then 1 else 0) := by
  by_cases h1 : 0 < a <;> by_cases h2 : a + 1 < n
  · have : (range n).filter (fun t => ad a t = 1) = {a - 1, a + 1} := by
      ext t; rw [mem_filter]; simp only [mem_range, mem_insert, mem_singleton, ad]; omega
    rw [this, card_pair (by omega)]; simp [h1, h2]
  · have : (range n).filter (fun t => ad a t = 1) = {a - 1} := by
      ext t; rw [mem_filter]; simp only [mem_range, mem_singleton, ad]; omega
    rw [this]; simp [h1, h2]
  · have : (range n).filter (fun t => ad a t = 1) = {a + 1} := by
      ext t; rw [mem_filter]; simp only [mem_range, mem_singleton, ad]; omega
    rw [this]; simp [h1, h2]
  · have : (range n).filter (fun t => ad a t = 1) = ∅ := by
      ext t; rw [mem_filter]; simp only [mem_range, ad, Finset.notMem_empty, iff_false]; omega
    rw [this]; simp [h1, h2]

lemma degree_eq (v : C.V) [Fintype (C.graph.neighborSet v)] :
    C.graph.degree v = ∑ w, if C.d v w = 1 then 1 else 0 := by
  classical
  rw [← card_neighborFinset_eq_degree, ← Finset.card_filter]
  congr 1; ext w
  simp [mem_neighborFinset, ← dist_eq_one_iff_adj, C.dist_eq]

/-- **Degree of a spine vertex.** -/
theorem degree_spine (s : Fin (C.S + 1)) [Fintype (C.graph.neighborSet (.inl s))] :
    C.graph.degree (.inl s) = (if 0 < s.val then 1 else 0) + (if s.val + 1 < C.S + 1 then 1 else 0) +
      #(univ.filter (fun i => C.c i = s.val ∧ 0 < C.ℓ i)) := by
  rw [degree_eq, Fintype.sum_sum_type, Fintype.sum_sigma, Finset.card_filter]
  show (∑ t : Fin (C.S + 1), if ad s.val t.val = 1 then 1 else 0) +
      ∑ i, ∑ j : Fin (C.ℓ i), (if ad s.val (C.c i) + (j.val + 1) = 1 then 1 else 0) = _
  have h1 := cnt (C.S + 1) (fun t => ad s.val t = 1)
  rw [h1, cnt_ad _ _ s.isLt]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [cnt (C.ℓ i) (fun j => ad s.val (C.c i) + (j + 1) = 1)]
  by_cases hi : C.c i = s.val ∧ 0 < C.ℓ i
  · have : (range (C.ℓ i)).filter (fun j => ad s.val (C.c i) + (j + 1) = 1) = {0} := by
      ext j; rw [mem_filter]; simp only [mem_range, mem_singleton, ad]; omega
    rw [this, if_pos hi]; rfl
  · have : (range (C.ℓ i)).filter (fun j => ad s.val (C.c i) + (j + 1) = 1) = ∅ := by
      ext j; rw [mem_filter]; simp only [mem_range, ad, Finset.notMem_empty, iff_false]; omega
    rw [this, if_neg hi]; rfl

/-- **Degree of an arm vertex.** -/
theorem degree_arm (i : Fin C.k) (j : Fin (C.ℓ i)) [Fintype (C.graph.neighborSet (.inr ⟨i, j⟩))] :
    C.graph.degree (.inr ⟨i, j⟩) = 1 + (if j.val + 1 < C.ℓ i then 1 else 0) := by
  rw [degree_eq, Fintype.sum_sum_type, Fintype.sum_sigma]
  show (∑ t : Fin (C.S + 1), if ad t.val (C.c i) + (j.val + 1) = 1 then 1 else 0) +
      ∑ i', ∑ j' : Fin (C.ℓ i'), (if (if i = i' then ad j.val j'.val
        else (j.val + 1) + ad (C.c i) (C.c i') + (j'.val + 1)) = 1 then 1 else 0) = _
  have h1 := cnt (C.S + 1) (fun t => ad t (C.c i) + (j.val + 1) = 1)
  rw [h1]
  have e1 : (range (C.S + 1)).filter (fun t => ad t (C.c i) + (j.val + 1) = 1) =
      if j.val = 0 then {C.c i} else ∅ := by
    have := C.hc i
    split_ifs with hj
    · ext t; rw [mem_filter]; simp only [mem_range, mem_singleton, ad]; omega
    · ext t; rw [mem_filter]; simp only [mem_range, ad, Finset.notMem_empty, iff_false]; omega
  rw [e1, Finset.sum_eq_single i]
  · simp only [if_true]
    rw [cnt (C.ℓ i) (fun j' => ad j.val j' = 1), cnt_ad _ _ j.isLt]
    split_ifs <;> simp_all
  · intro i' _ hne
    refine Finset.sum_eq_zero fun j' _ => ?_
    rw [if_neg (Ne.symm hne), if_neg (by omega)]
  · simp

lemma degree_arm_le (x : Σ i : Fin C.k, Fin (C.ℓ i)) [Fintype (C.graph.neighborSet (.inr x))] : C.graph.degree (.inr x) ≤ 2 := by
  obtain ⟨i, j⟩ := x
  rw [degree_arm]; split_ifs <;> omega

open Classical in
lemma arm_not_branch (x : Σ i : Fin C.k, Fin (C.ℓ i)) : (.inr x : C.V) ∉ C.branch := by
  simp only [branch, mem_filter, mem_univ, true_and, not_le]
  have := C.degree_arm_le x; omega

end Cat

/-- **`T` has exactly three branch vertices**: spine vertices `0`, `53` and `76`. -/
theorem T_branch : T.branch = {.inl 0, .inl 53, .inl 76} := by
  ext v
  rcases v with s | x
  · simp only [Cat.branch, mem_filter, mem_univ, true_and, mem_insert, mem_singleton, Sum.inl.injEq]
    rw [Cat.degree_spine]
    revert s; decide
  · simp only [mem_insert, mem_singleton, reduceCtorEq, or_self, iff_false]
    exact T.arm_not_branch x

lemma T_branch_card : T.branch.card = 3 := by rw [T_branch]; decide

lemma card_k {C : Cat} {M : Multiset ℕ} (h : Finset.univ.val.map C.ℓ = M) : C.k = Multiset.card M := by
  rw [← h]; simp

/-- **A starlike caterpillar has exactly one branch vertex.** -/
theorem Starlike.branch {C : Cat} (H : Starlike C) : C.branch = {.inl ⟨0, by omega⟩} := by
  have hk : C.k = 12 := by rw [card_k H.hD]; rfl
  ext v
  rcases v with s | x
  · have hs : s.val = 0 := by have := s.isLt; have := H.hS; omega
    have hall : univ.filter (fun i => C.c i = s.val ∧ 0 < C.ℓ i) = univ := by
      ext i; simp only [mem_filter, mem_univ, true_and, iff_true]
      exact ⟨by have := C.hc i; have := H.hS; omega, H.hℓ i⟩
    simp only [Cat.branch, mem_filter, mem_univ, true_and, Cat.degree_spine, mem_singleton, Sum.inl.injEq,
      hall, card_univ, Fintype.card_fin, hk]
    constructor
    · intro _; exact Fin.ext hs
    · intro _; split_ifs <;> omega
  · simp only [mem_singleton, reduceCtorEq, iff_false]
    exact C.arm_not_branch x

/-- **A two-hub caterpillar has exactly two branch vertices**, the ends of its spine. -/
theorem TwoHub.branch {C : Cat} (H : TwoHub C) :
    C.branch = {.inl ⟨0, by omega⟩, .inl ⟨C.S, by omega⟩} := by
  ext v
  rcases v with s | x
  · simp only [Cat.branch, mem_filter, mem_univ, true_and, Cat.degree_spine, mem_insert, mem_singleton,
      Sum.inl.injEq, Fin.ext_iff]
    have hS := H.hS
    have hs := s.isLt
    by_cases h0 : s.val = 0
    · have : 2 ≤ #(univ.filter (fun i => C.c i = s.val ∧ 0 < C.ℓ i)) := by
        refine le_trans H.hA (card_le_card fun i hi => ?_)
        simp only [mem_filter, mem_univ, true_and] at hi ⊢; exact ⟨by omega, H.hℓ i⟩
      simp only [h0] at this ⊢; simp only [true_or, iff_true]; split_ifs <;> omega
    by_cases hS' : s.val = C.S
    · have : 2 ≤ #(univ.filter (fun i => C.c i = s.val ∧ 0 < C.ℓ i)) := by
        refine le_trans H.hB (card_le_card fun i hi => ?_)
        simp only [mem_filter, mem_univ, true_and] at hi ⊢; exact ⟨by omega, H.hℓ i⟩
      simp only [hS'] at this ⊢; simp only [or_true, iff_true]; split_ifs <;> omega
    · have : univ.filter (fun i => C.c i = s.val ∧ 0 < C.ℓ i) = ∅ := by
        ext i; simp only [mem_filter, mem_univ, true_and, Finset.notMem_empty, iff_false, not_and]
        intro h; rcases H.hc i with h' | h' <;> omega
      simp only [this, card_empty, h0, hS', or_self, iff_false]; split_ifs <;> omega
  · simp only [mem_insert, mem_singleton, reduceCtorEq, or_self, iff_false]
    exact C.arm_not_branch x

end Remoteness
