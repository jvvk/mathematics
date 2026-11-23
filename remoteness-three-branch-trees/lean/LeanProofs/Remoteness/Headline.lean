import LeanProofs.Remoteness.Transmission
import LeanProofs.Remoteness.Obstruction

/-!
# The headline: `T` beats every starlike and every two-branch tree with segment sequence `D`

`D = (53, 23, 21, 9, 9, 9, 1^6)`. The counterexample `T` is the caterpillar with spine `0..76` (segments `53` and
`23`) and arms `9, 9, 9` at `0`, `21` at `53`, and six `1`s at `76`. A starlike `D`-tree is a caterpillar with
`S = 0` and arm lengths `D`; a tree with two branch vertices is a caterpillar whose spine is one segment of length
`S > 0` with at least two arms at each end, and `S` together with the arm lengths is `D`.

We prove: every vertex of `T` has transmission at most `5962` (with equality at the unit leaves), and every
starlike or two-branch `D`-tree has a vertex of transmission at least `5971`. All these trees have `n = 131`
vertices, so this compares remoteness.
-/

namespace Remoteness

open Cat

/-- The segment sequence. -/
def Dseq : Multiset ℕ := {53, 23, 21, 9, 9, 9, 1, 1, 1, 1, 1, 1}

/-- The counterexample `T`. -/
abbrev T : Cat where
  S := 76
  k := 10
  c := ![0, 0, 0, 53, 76, 76, 76, 76, 76, 76]
  ℓ := ![9, 9, 9, 21, 1, 1, 1, 1, 1, 1]
  hc := by decide

lemma T_pos (i : Fin 10) : 0 < T.ℓ i := by fin_cases i <;> decide

/-- The ten leaf values of `T` (twice the transmission), from the closed form `two_trans_leaf`. -/
lemma T_leaf_values (i : Fin 10) : 2 * T.trans (T.leaf i (T_pos i)) ≤ 2 * 5962 := by
  rw [two_trans_leaf]
  fin_cases i <;> decide

lemma T_leaf_unit : T.trans (T.leaf 4 (T_pos 4)) = 5962 := by
  have h := two_trans_leaf T 4 (T_pos 4)
  have : 2 * T.trans (T.leaf 4 (T_pos 4)) = 2 * 5962 := by rw [h]; decide
  omega

/-- **Every vertex of `T` has transmission at most `5962`** (Lemma 2.2 for `T`: each vertex lies on a path between
two leaves, and transmission along such a path is at most the larger end's). -/
theorem T_trans_le (v : T.V) : T.trans v ≤ 5962 := by
  have hl (i : Fin 10) : T.trans (T.leaf i (T_pos i)) ≤ 5962 := by have := T_leaf_values i; omega
  have h0 : (0 : Fin 10) ≠ 4 := by decide
  rcases v with u | ⟨i, j⟩
  · have hu := u.isLt
    have := trans_spine_le (C := T) 0 4 h0 (by decide) (T_pos 0) (T_pos 4) u (by simp [T])
      (by have h := u.isLt; change (u : ℕ) < 77 at h; change (u : ℕ) ≤ 76; omega)
    exact this.trans (max_le (hl 0) (hl 4))
  · -- arms at 0 or 53 lie on the path to arm 4; the unit arms at 76 lie on the path from arm 0
    have hci : T.c i ≤ 76 := T.hc i
    by_cases h4 : i.val < 4
    · have hne : i ≠ 4 := by intro h; subst h; simp at h4
      have := trans_armL_le (C := T) i 4 hne (by fin_cases i <;> simp_all [T]) (T_pos i) (T_pos 4) j
      exact this.trans (max_le (hl i) (hl 4))
    · have hne : (0 : Fin 10) ≠ i := by intro h; subst h; simp at h4
      have := trans_armR_le (C := T) 0 i hne (by simp) (T_pos 0) (T_pos i) j
      exact this.trans (max_le (hl 0) (hl i))

/-- Starlike `D`-trees as caterpillars. -/
structure Starlike (C : Cat) : Prop where
  hS : C.S = 0
  hℓ : ∀ i, 0 < C.ℓ i
  hD : Finset.univ.val.map C.ℓ = Dseq

/-- `D`-trees with two branch vertices as caterpillars. -/
structure TwoHub (C : Cat) : Prop where
  hS : 0 < C.S
  hc : ∀ i, C.c i = 0 ∨ C.c i = C.S
  hA : 2 ≤ (Finset.univ.filter (fun i => C.c i = 0)).card
  hB : 2 ≤ (Finset.univ.filter (fun i => C.c i = C.S)).card
  hℓ : ∀ i, 0 < C.ℓ i
  hD : C.S ::ₘ Finset.univ.val.map C.ℓ = Dseq

section Lower

variable (C : Cat)

/-- Leaf transmission when every arm hangs at an end of the spine (the starlike and two-branch case). -/
lemma two_trans_leaf_ends (hc : ∀ i, C.c i = 0 ∨ C.c i = C.S) (i : Fin C.k) (hi : 0 < C.ℓ i) :
    2 * C.trans (C.leaf i hi) =
      C.S * (C.S + 1) + ∑ i', C.ℓ i' * (C.ℓ i' + 1) +
        2 * C.ℓ i * (C.S + ∑ i' ∈ Finset.univ.erase i, C.ℓ i') +
        2 * C.S * ∑ i' ∈ Finset.univ.filter (fun i' => C.c i' ≠ C.c i), C.ℓ i' := by
  rw [two_trans_leaf]
  have hcc : C.c i * (C.c i + 1) + (C.S - C.c i) * (C.S - C.c i + 1) = C.S * (C.S + 1) := by
    rcases hc i with h | h <;> rw [h] <;> simp
  have had (i' : Fin C.k) : ad (C.c i) (C.c i') = if C.c i' ≠ C.c i then C.S else 0 := by
    rcases hc i with h | h <;> rcases hc i' with h' | h' <;> simp [ad, h, h'] <;> omega
  have hsplit : ∑ i' ∈ Finset.univ.erase i,
      (2 * C.ℓ i' * (C.ℓ i + ad (C.c i) (C.c i')) + C.ℓ i' * (C.ℓ i' + 1)) =
      2 * C.ℓ i * ∑ i' ∈ Finset.univ.erase i, C.ℓ i' +
        2 * C.S * ∑ i' ∈ Finset.univ.filter (fun i' => C.c i' ≠ C.c i), C.ℓ i' +
        ∑ i' ∈ Finset.univ.erase i, C.ℓ i' * (C.ℓ i' + 1) := by
    simp only [had, Finset.sum_add_distrib, mul_add, Finset.mul_sum]
    congr 1
    · congr 1
      · apply Finset.sum_congr rfl; intro x _; ring
      · rw [Finset.sum_filter]
        rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
        simp only [ne_eq, not_true_eq_false, if_false, add_zero]
        apply Finset.sum_congr rfl; intro x _; split_ifs <;> ring
  have hall : ∑ i', C.ℓ i' * (C.ℓ i' + 1) =
      C.ℓ i * (C.ℓ i + 1) + ∑ i' ∈ Finset.univ.erase i, C.ℓ i' * (C.ℓ i' + 1) :=
    (Finset.add_sum_erase _ _ (Finset.mem_univ i)).symm
  rw [hcc, hsplit, hall]
  have : C.ℓ i * (C.ℓ i - 1) + 2 * C.ℓ i = C.ℓ i * (C.ℓ i + 1) := by
    cases h : C.ℓ i with
    | zero => omega
    | succ n => simp; ring
  nlinarith [this]

lemma Dseq_eq : Dseq = 53 ::ₘ Dp := by decide

/-- Sums over the arms from the multiset of arm lengths. -/
lemma arm_sums {C : Cat} {M : Multiset ℕ} (h : Finset.univ.val.map C.ℓ = M) :
    ∑ i, C.ℓ i = M.sum ∧ ∑ i, C.ℓ i * (C.ℓ i + 1) = (M.map (fun x => x * (x + 1))).sum := by
  constructor
  · rw [Finset.sum_eq_multiset_sum, h]
  · rw [Finset.sum_eq_multiset_sum, ← h, Multiset.map_map]; rfl

/-- An arm of length `53` has a leaf of transmission at least `6160` (the starlike value). -/
lemma ge_of_arm53 (hc : ∀ i, C.c i = 0 ∨ C.c i = C.S) (hN : C.S + ∑ i, C.ℓ i = 130)
    (hQ : C.S * (C.S + 1) + ∑ i, C.ℓ i * (C.ℓ i + 1) = 4158)
    (i : Fin C.k) (hi : 0 < C.ℓ i) (h53 : C.ℓ i = 53) : 6160 ≤ C.trans (C.leaf i hi) := by
  have h := two_trans_leaf_ends C hc i hi
  have hsum : C.S + ∑ i' ∈ Finset.univ.erase i, C.ℓ i' = 77 := by
    have := Finset.add_sum_erase Finset.univ C.ℓ (Finset.mem_univ i); omega
  rw [hsum, h53, hQ] at h
  have : 4158 + 2 * 53 * 77 ≤ 2 * C.trans (C.leaf i hi) := by rw [h]; exact Nat.le_add_right _ _
  omega

/-- Leaf value in a two-branch tree with joining segment `53` (doubled, over `ℤ`). -/
lemma leaf_bar53 (H : TwoHub C) (hS : C.S = 53) (i : Fin C.k) :
    (2 * C.trans (C.leaf i (H.hℓ i)) : ℤ) =
      4158 + 2 * (C.ℓ i : ℤ) * (130 - C.ℓ i) +
        106 * ((∑ i' ∈ Finset.univ.filter (fun i' => C.c i' ≠ C.c i), C.ℓ i' : ℕ) : ℤ) := by
  have h := two_trans_leaf_ends C H.hc i (H.hℓ i)
  have hmap : Finset.univ.val.map C.ℓ = Dp := by
    have := H.hD; rw [hS, Dseq_eq] at this; exact (Multiset.cons_inj_right 53).mp this
  obtain ⟨hN, hQ⟩ := arm_sums hmap
  have hN' : ∑ i, C.ℓ i = 77 := by rw [hN]; decide
  have hQ' : ∑ i, C.ℓ i * (C.ℓ i + 1) = 1296 := by rw [hQ]; decide
  have hsum : C.S + ∑ i' ∈ Finset.univ.erase i, C.ℓ i' = 130 - C.ℓ i := by
    have := Finset.add_sum_erase Finset.univ C.ℓ (Finset.mem_univ i); omega
  have hle : C.ℓ i ≤ 77 := by
    have := Finset.single_le_sum (fun j _ => Nat.zero_le (C.ℓ j)) (Finset.mem_univ i); omega
  rw [hsum, hQ', hS] at h
  have hcast : ((130 - C.ℓ i : ℕ) : ℤ) = 130 - C.ℓ i := by omega
  have := congrArg (fun n : ℕ => (n : ℤ)) h
  push_cast [hcast] at this
  rw [this]; push_cast; ring

/-- A two-branch tree with joining segment `53` has a leaf of transmission at least `5971` (Lemma 3.2). -/
lemma ge_of_bar53 (H : TwoHub C) (hS : C.S = 53) : ∃ v, 5971 ≤ C.trans v := by
  have hmap : Finset.univ.val.map C.ℓ = Dp := by
    have := H.hD; rw [hS, Dseq_eq] at this; exact (Multiset.cons_inj_right 53).mp this
  set F0 := Finset.univ.filter (fun i => C.c i = 0)
  set F1 := Finset.univ.filter (fun i => C.c i = C.S)
  have hcomp : ∀ i, C.c i ≠ 0 ↔ C.c i = C.S := by
    intro i; have := H.hS; rcases H.hc i with h | h <;> simp [h] <;> omega
  have e1 : F1.val = Multiset.filter (fun i => ¬ C.c i = 0) Finset.univ.val := by
    rw [Finset.filter_val]; exact Multiset.filter_congr (fun i _ => (hcomp i).symm)
  have hAB : F0.val.map C.ℓ + F1.val.map C.ℓ = Dp := by
    rw [e1, Finset.filter_val, ← Multiset.map_add, Multiset.filter_add_not, hmap]
  have hob := obstruction _ _ hAB
  simp only [broom, le_max_iff] at hob
  have opp0 (i : Fin C.k) (hi : C.c i = 0) :
      Finset.univ.filter (fun i' => C.c i' ≠ C.c i) = F1 := by
    ext x; simp only [Finset.mem_filter, Finset.mem_univ, true_and, F1, hi]; exact hcomp x
  have opp1 (i : Fin C.k) (hi : C.c i = C.S) :
      Finset.univ.filter (fun i' => C.c i' ≠ C.c i) = F0 := by
    ext x; simp only [Finset.mem_filter, Finset.mem_univ, true_and, F0, hi]
    constructor
    · intro h; by_contra h0; exact h ((hcomp x).mp h0)
    · intro h0 h; rw [h0] at h; have := H.hS; omega
  rcases hob with hA | hB
  · obtain ⟨i, hiG, hsup⟩ := Finset.exists_mem_eq_sup F0
      (Finset.card_pos.mp (lt_of_lt_of_le (by norm_num) H.hA)) C.ℓ
    have hci : C.c i = 0 := (Finset.mem_filter.mp hiG).2
    refine ⟨C.leaf i (H.hℓ i), ?_⟩
    have h := leaf_bar53 C H hS i
    rw [opp0 i hci] at h
    rw [← Finset.sup_def, hsup, ← Finset.sum_eq_multiset_sum] at hA
    simp only [f] at hA
    have : (11942 : ℤ) ≤ 2 * C.trans (C.leaf i (H.hℓ i)) := by rw [h]; linarith
    omega
  · obtain ⟨i, hiG, hsup⟩ := Finset.exists_mem_eq_sup F1
      (Finset.card_pos.mp (lt_of_lt_of_le (by norm_num) H.hB)) C.ℓ
    have hci : C.c i = C.S := (Finset.mem_filter.mp hiG).2
    refine ⟨C.leaf i (H.hℓ i), ?_⟩
    have h := leaf_bar53 C H hS i
    rw [opp1 i hci] at h
    rw [← Finset.sup_def, hsup, ← Finset.sum_eq_multiset_sum] at hB
    simp only [f] at hB
    have : (11942 : ℤ) ≤ 2 * C.trans (C.leaf i (H.hℓ i)) := by rw [h]; linarith
    omega

/-- **Headline.** Every vertex of `T` has transmission at most `5962`, and every starlike or two-branch
`D`-tree has a vertex of transmission at least `5971`. -/
theorem headline :
    (∀ v, T.trans v ≤ 5962) ∧ (∃ v, T.trans v = 5962) ∧
      ∀ C : Cat, Starlike C ∨ TwoHub C → ∃ v, 5971 ≤ C.trans v := by
  refine ⟨T_trans_le, ⟨_, T_leaf_unit⟩, ?_⟩
  intro C hC
  rcases hC with H | H
  · -- starlike: the arm of length 53
    have hc : ∀ i, C.c i = 0 ∨ C.c i = C.S := fun i => Or.inl (by have := C.hc i; rw [H.hS] at this; omega)
    obtain ⟨hN, hQ⟩ := arm_sums H.hD
    obtain ⟨i, -, hi53⟩ := Multiset.mem_map.mp (show 53 ∈ Finset.univ.val.map C.ℓ by rw [H.hD]; decide)
    exact ⟨_, le_trans (by norm_num) (ge_of_arm53 C hc (by rw [H.hS, hN]; decide)
      (by rw [H.hS, hQ]; decide) i (H.hℓ i) hi53)⟩
  · by_cases hS : C.S = 53
    · exact ge_of_bar53 C H hS
    · -- the 53 is an arm
      have hD := H.hD
      have hmem : 53 ∈ C.S ::ₘ Finset.univ.val.map C.ℓ := by rw [hD]; decide
      have harm : 53 ∈ Finset.univ.val.map C.ℓ := by
        rcases Multiset.mem_cons.mp hmem with h | h
        · exact absurd h.symm hS
        · exact h
      obtain ⟨i, -, hi53⟩ := Multiset.mem_map.mp harm
      have hsum := congrArg Multiset.sum hD
      have hsq := congrArg (fun m => (m.map (fun x => x * (x + 1))).sum) hD
      simp only [Multiset.sum_cons, Multiset.map_cons] at hsum hsq
      obtain ⟨hN, hQ⟩ := arm_sums (M := Finset.univ.val.map C.ℓ) rfl
      exact ⟨_, le_trans (by norm_num) (ge_of_arm53 C H.hc (by rw [hN, hsum]; decide)
        (by rw [hQ]; rw [hsq]; decide) i (H.hℓ i) hi53)⟩

end Lower

end Remoteness
