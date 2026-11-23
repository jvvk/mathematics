import LeanProofs.Remoteness.Caterpillar

/-!
# Transmission in caterpillars with legs

`trans v = ∑ w, dist v w`. We compute it at the leaf of an arm in closed form (the family case of Lemma 2.1 of
the note) and prove that along any leaf-to-leaf path through the spine every vertex has transmission at most the
larger of the two leaves' (the family case of Lemma 2.2), by convexity of each distance term along the path.
-/

namespace Remoteness

namespace Cat

variable (C : Cat)

/-- Transmission, with the closed-form distance (equal to the graph distance by `dist_eq`). -/
def trans (v : C.V) : ℕ := ∑ w, C.d v w

lemma trans_eq_sum_dist (v : C.V) : C.trans v = ∑ w, C.graph.dist v w := by
  simp [trans, dist_eq]

lemma two_sum_rev (n : ℕ) : 2 * ∑ s ∈ Finset.range (n + 1), (n - s) = n * (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ']
    have : ∑ s ∈ Finset.range (n + 1), (n + 1 - (s + 1)) = ∑ s ∈ Finset.range (n + 1), (n - s) := by
      apply Finset.sum_congr rfl; intro s _; omega
    rw [this, mul_add, ih]; simp; ring

/-- `2 ∑_{s=0}^{S} |s - c| = c (c + 1) + (S - c)(S - c + 1)` for `c ≤ S`. -/
lemma two_sum_ad (S c : ℕ) (hc : c ≤ S) :
    2 * ∑ s ∈ Finset.range (S + 1), ad s c = c * (c + 1) + (S - c) * (S - c + 1) := by
  induction S with
  | zero => obtain rfl : c = 0 := by omega
            simp [ad]
  | succ S ih =>
    rcases Nat.eq_or_lt_of_le hc with h | h
    · subst h
      have : ∑ s ∈ Finset.range (S + 1 + 1), ad s (S + 1) = ∑ s ∈ Finset.range (S + 1 + 1), (S + 1 - s) := by
        apply Finset.sum_congr rfl; intro s hs; simp at hs; simp [ad]; omega
      rw [this, two_sum_rev]; simp
    · rw [Finset.sum_range_succ, mul_add, ih (by omega)]
      have e1 : ad (S + 1) c = S + 1 - c := by simp [ad]; omega
      rw [e1]
      have e2 : S + 1 - c = S - c + 1 := by omega
      rw [e2]; ring

lemma two_sum_succ (m : ℕ) : 2 * ∑ j ∈ Finset.range m, (j + 1) = m * (m + 1) := by
  induction m with
  | zero => simp
  | succ m ih => rw [Finset.sum_range_succ, mul_add, ih]; ring

/-- The leaf of arm `i`. -/
def leaf (i : Fin C.k) (hi : 0 < C.ℓ i) : C.V := .inr ⟨i, ⟨C.ℓ i - 1, by omega⟩⟩

/-- **Lemma 2.1 for caterpillars** (doubled): the transmission of the leaf of arm `i`. -/
theorem two_trans_leaf (i : Fin C.k) (hi : 0 < C.ℓ i) :
    2 * C.trans (C.leaf i hi) =
      2 * (C.S + 1) * C.ℓ i + (C.c i * (C.c i + 1) + (C.S - C.c i) * (C.S - C.c i + 1)) +
        C.ℓ i * (C.ℓ i - 1) +
        ∑ i' ∈ Finset.univ.erase i,
          (2 * C.ℓ i' * (C.ℓ i + ad (C.c i) (C.c i')) + C.ℓ i' * (C.ℓ i' + 1)) := by
  simp only [trans, leaf, Fintype.sum_sum_type, Fintype.sum_sigma]
  rw [mul_add, ← Finset.add_sum_erase _ _ (Finset.mem_univ i), mul_add]
  -- spine part
  have hspine : 2 * ∑ s : Fin (C.S + 1), C.d (.inr ⟨i, ⟨C.ℓ i - 1, by omega⟩⟩) (.inl s) =
      2 * (C.S + 1) * C.ℓ i + (C.c i * (C.c i + 1) + (C.S - C.c i) * (C.S - C.c i + 1)) := by
    simp only [d]
    rw [Fin.sum_univ_eq_sum_range (fun s => ad s (C.c i) + (C.ℓ i - 1 + 1)), Finset.sum_add_distrib,
      mul_add, two_sum_ad _ _ (C.hc i)]
    simp; have : C.ℓ i - 1 + 1 = C.ℓ i := by omega
    rw [this]; ring
  -- own arm
  have hown : 2 * ∑ j : Fin (C.ℓ i), C.d (.inr ⟨i, ⟨C.ℓ i - 1, by omega⟩⟩) (.inr ⟨i, j⟩) =
      C.ℓ i * (C.ℓ i - 1) := by
    simp only [d, if_true]
    rw [Fin.sum_univ_eq_sum_range (fun j => ad (C.ℓ i - 1) j)]
    have : ∑ j ∈ Finset.range (C.ℓ i), ad (C.ℓ i - 1) j = ∑ j ∈ Finset.range (C.ℓ i - 1 + 1), (C.ℓ i - 1 - j) := by
      rw [show C.ℓ i - 1 + 1 = C.ℓ i by omega]
      apply Finset.sum_congr rfl; intro j hj; simp at hj; simp [ad]; omega
    rw [this, two_sum_rev, show C.ℓ i - 1 + 1 = C.ℓ i by omega, mul_comm]
  -- other arms
  have hother : 2 * ∑ i' ∈ Finset.univ.erase i, ∑ j : Fin (C.ℓ i'),
      C.d (.inr ⟨i, ⟨C.ℓ i - 1, by omega⟩⟩) (.inr ⟨i', j⟩) =
      ∑ i' ∈ Finset.univ.erase i,
          (2 * C.ℓ i' * (C.ℓ i + ad (C.c i) (C.c i')) + C.ℓ i' * (C.ℓ i' + 1)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i' hi'
    have hne : i ≠ i' := fun h => (Finset.mem_erase.mp hi').1 (h ▸ rfl)
    simp only [d, hne, if_false]
    rw [Fin.sum_univ_eq_sum_range (fun j => C.ℓ i - 1 + 1 + ad (C.c i) (C.c i') + (j + 1)),
      Finset.sum_add_distrib, mul_add, two_sum_succ]
    simp; rw [show C.ℓ i - 1 + 1 = C.ℓ i by omega]; ring
  rw [hspine, hown, hother]; ring

/-- Convexity of `t ↦ |t - a| + h` on `[0, m]`, in weighted form. -/
lemma convex_ad (m t a h : ℕ) (ht : t ≤ m) (ha : a ≤ m) :
    m * (ad t a + h) ≤ (m - t) * (a + h) + t * (m - a + h) := by
  simp only [ad]
  rcases le_total t a with hta | hta
  · have e1 : t - a = 0 := by omega
    rw [e1]
    obtain ⟨u, rfl⟩ : ∃ u, a = t + u := ⟨a - t, by omega⟩
    obtain ⟨v, rfl⟩ : ∃ v, m = t + u + v := ⟨m - (t + u), by omega⟩
    have e2 : t + u - t = u := by omega
    have e3 : t + u + v - t = u + v := by omega
    have e4 : t + u + v - (t + u) = v := by omega
    rw [e2, e3, e4]; nlinarith
  · have e1 : a - t = 0 := by omega
    rw [e1]
    obtain ⟨u, rfl⟩ : ∃ u, t = a + u := ⟨t - a, by omega⟩
    obtain ⟨v, rfl⟩ : ∃ v, m = a + u + v := ⟨m - (a + u), by omega⟩
    have e2 : a + u - a = u := by omega
    have e3 : a + u + v - (a + u) = v := by omega
    have e4 : a + u + v - a = u + v := by omega
    rw [e2, e3, e4]; nlinarith

/-- If every vertex `w` sees the path with a profile `|t - a| + h`, then `v` (at position `t`) has transmission at
most the larger of the two ends'. -/
lemma trans_le_of_profile (v L1 L2 : C.V) (m t : ℕ) (hm : 0 < m) (ht : t ≤ m)
    (hprof : ∀ w, ∃ a h, a ≤ m ∧ C.d L1 w = a + h ∧ C.d L2 w = m - a + h ∧ C.d v w = ad t a + h) :
    C.trans v ≤ max (C.trans L1) (C.trans L2) := by
  have key : m * C.trans v ≤ (m - t) * C.trans L1 + t * C.trans L2 := by
    simp only [trans, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum; intro w _
    obtain ⟨a, h, ha, h1, h2, h3⟩ := hprof w
    rw [h1, h2, h3]; exact convex_ad m t a h ht ha
  have hmax : (m - t) * C.trans L1 + t * C.trans L2 ≤ m * max (C.trans L1) (C.trans L2) := by
    have h1 := le_max_left (C.trans L1) (C.trans L2)
    have h2 := le_max_right (C.trans L1) (C.trans L2)
    have : m = (m - t) + t := by omega
    calc (m - t) * C.trans L1 + t * C.trans L2
        ≤ (m - t) * max (C.trans L1) (C.trans L2) + t * max (C.trans L1) (C.trans L2) := by gcongr
      _ = m * max (C.trans L1) (C.trans L2) := by rw [← add_mul, ← this]
  exact le_of_mul_le_mul_left (key.trans hmax) hm

section Path

variable {C} (i i' : Fin C.k) (hii : i ≠ i') (hci : C.c i ≤ C.c i') (hi : 0 < C.ℓ i) (hi' : 0 < C.ℓ i')

/-- Length of the path from the leaf of arm `i` through the spine to the leaf of arm `i'`. -/
def pathLen : ℕ := C.ℓ i + (C.c i' - C.c i) + C.ℓ i'

include hii hci hi hi' in
/-- The profile of a vertex `w` along the path, and the ends' distances. -/
lemma ends_profile (w : C.V) :
    ∃ a h, a ≤ pathLen i i' ∧ C.d (C.leaf i hi) w = a + h ∧ C.d (C.leaf i' hi') w = pathLen i i' - a + h ∧
      (∀ u : Fin (C.S + 1), C.c i ≤ u.val → u.val ≤ C.c i' →
        C.d (.inl u) w = ad (C.ℓ i + (u.val - C.c i)) a + h) ∧
      (∀ j : Fin (C.ℓ i), C.d (.inr ⟨i, j⟩) w = ad (C.ℓ i - 1 - j.val) a + h) ∧
      (∀ j : Fin (C.ℓ i'), C.d (.inr ⟨i', j⟩) w = ad (C.ℓ i + (C.c i' - C.c i) + j.val + 1) a + h) := by
  have hcS := C.hc i; have hcS' := C.hc i'
  rcases w with u | ⟨i₂, j'⟩
  · have hu := u.isLt
    refine ⟨C.ℓ i + (min (max u.val (C.c i)) (C.c i') - C.c i), (C.c i - u.val) + (u.val - C.c i'),
      ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [pathLen]; omega
    · simp only [d, leaf, ad]; omega
    · simp only [d, leaf, ad, pathLen]; omega
    · intro x h1 h2; simp only [d, ad]; omega
    · intro j; have := j.isLt; simp only [d, ad]; omega
    · intro j; have := j.isLt; simp only [d, ad]; omega
  · have hj' := j'.isLt
    by_cases h1 : i₂ = i
    · subst h1
      refine ⟨C.ℓ i₂ - 1 - j'.val, 0, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp only [pathLen]; omega
      · simp only [d, leaf, ad, if_true]; omega
      · simp only [d, leaf, ad, pathLen, if_neg (Ne.symm hii)]; omega
      · intro x h1 h2; simp only [d, ad]; omega
      · intro j; have := j.isLt; simp only [d, ad, if_true]; omega
      · intro j; have := j.isLt; simp only [d, ad, if_neg (Ne.symm hii)]; omega
    · by_cases h2 : i₂ = i'
      · subst h2
        refine ⟨C.ℓ i + (C.c i₂ - C.c i) + j'.val + 1, 0, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · simp only [pathLen]; omega
        · simp only [d, leaf, ad, if_neg hii]; omega
        · simp only [d, leaf, ad, pathLen, if_true]; omega
        · intro x h1 h2; simp only [d, ad]; omega
        · intro j; have := j.isLt; simp only [d, ad, if_neg hii]; omega
        · intro j; have := j.isLt; simp only [d, ad, if_true]; omega
      · have hc2 := C.hc i₂
        refine ⟨C.ℓ i + (min (max (C.c i₂) (C.c i)) (C.c i') - C.c i),
          (C.c i - C.c i₂) + (C.c i₂ - C.c i') + (j'.val + 1), ?_, ?_, ?_, ?_, ?_, ?_⟩
        · simp only [pathLen]; omega
        · simp only [d, leaf, ad, if_neg (Ne.symm h1)]; omega
        · simp only [d, leaf, ad, pathLen, if_neg (Ne.symm h2)]; omega
        · intro x h1 h2; simp only [d, ad]; omega
        · intro j; have := j.isLt; simp only [d, ad, if_neg (Ne.symm h1)]; omega
        · intro j; have := j.isLt; simp only [d, ad, if_neg (Ne.symm h2)]; omega

include hii hci hi hi' in
/-- **Lemma 2.2 for caterpillars**, on the spine between the two arms. -/
theorem trans_spine_le (u : Fin (C.S + 1)) (h1 : C.c i ≤ u.val) (h2 : u.val ≤ C.c i') :
    C.trans (.inl u) ≤ max (C.trans (C.leaf i hi)) (C.trans (C.leaf i' hi')) := by
  apply trans_le_of_profile C _ _ _ (pathLen i i') (C.ℓ i + (u.val - C.c i))
    (by simp only [pathLen]; omega) (by simp only [pathLen]; omega)
  intro w
  obtain ⟨a, h, ha, e1, e2, e3, -, -⟩ := ends_profile i i' hii hci hi hi' w
  exact ⟨a, h, ha, e1, e2, e3 u h1 h2⟩

include hii hci hi hi' in
/-- **Lemma 2.2 for caterpillars**, on arm `i`. -/
theorem trans_armL_le (j : Fin (C.ℓ i)) :
    C.trans (.inr ⟨i, j⟩) ≤ max (C.trans (C.leaf i hi)) (C.trans (C.leaf i' hi')) := by
  apply trans_le_of_profile C _ _ _ (pathLen i i') (C.ℓ i - 1 - j.val)
    (by simp only [pathLen]; omega) (by simp only [pathLen]; omega)
  intro w
  obtain ⟨a, h, ha, e1, e2, -, e4, -⟩ := ends_profile i i' hii hci hi hi' w
  exact ⟨a, h, ha, e1, e2, e4 j⟩

include hii hci hi hi' in
/-- **Lemma 2.2 for caterpillars**, on arm `i'`. -/
theorem trans_armR_le (j : Fin (C.ℓ i')) :
    C.trans (.inr ⟨i', j⟩) ≤ max (C.trans (C.leaf i hi)) (C.trans (C.leaf i' hi')) := by
  apply trans_le_of_profile C _ _ _ (pathLen i i') (C.ℓ i + (C.c i' - C.c i) + j.val + 1)
    (by simp only [pathLen]; omega) (by simp only [pathLen]; have := j.isLt; omega)
  intro w
  obtain ⟨a, h, ha, e1, e2, -, -, e5⟩ := ends_profile i i' hii hci hi hi' w
  exact ⟨a, h, ha, e1, e2, e5 j⟩

end Path

end Cat

end Remoteness
