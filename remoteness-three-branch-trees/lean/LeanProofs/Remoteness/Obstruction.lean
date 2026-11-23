import Mathlib

/-!
# The arithmetic obstruction (Lemma 3.2 of the note)

For `D = (53, 23, 21, 9, 9, 9, 1^6)` we have `N = 130`, `f t = t (130 - t)`, and a tree with two branch vertices
joined by the segment of length `53`, with pendant multisets `A` and `B`, has value
`max (f (max A) + 53 * ΣB) (f (max B) + 53 * ΣA)` (Lemma 2.3). Lemma 3.2: every splitting `A + B = D'` of
`D' = {23, 21, 9, 9, 9, 1, 1, 1, 1, 1, 1}` has value at least `3892`, and `3892` is attained.

The proof follows the note: put `23` in `A`; then `ΣB ≤ 26`; then `max B ≤ 9`, so `B` consists of `j` nines
and `i` ones; then `ΣB = 9j + i` would have to be `25` or `26`, which is impossible for `j ≤ 3`, `i ≤ 6`.
-/

namespace Remoteness

/-- `f t = t (N - t)` with `N = 130`. -/
def f (t : ℤ) : ℤ := t * (130 - t)

/-- `D'`: the segment lengths other than the longest one. -/
def Dp : Multiset ℕ := {23, 21, 9, 9, 9, 1, 1, 1, 1, 1, 1}

/-- Value of the two-branch tree with joining segment `53` and pendant multisets `A`, `B` (Lemma 2.3). -/
def broom (A B : Multiset ℕ) : ℤ :=
  max (f (A.sup : ℕ) + 53 * (B.sum : ℕ)) (f (B.sup : ℕ) + 53 * (A.sum : ℕ))

lemma broom_comm (A B : Multiset ℕ) : broom A B = broom B A := by
  unfold broom; exact max_comm _ _

/-- The sub-multiset of `D'` with `a, b, c, d` copies of `23, 21, 9, 1`. -/
def ms (a b c d : ℕ) : Multiset ℕ :=
  Multiset.replicate a 23 + Multiset.replicate b 21 + Multiset.replicate c 9 + Multiset.replicate d 1

lemma count_ms (a b c d x : ℕ) : (ms a b c d).count x =
    if x = 23 then a else if x = 21 then b else if x = 9 then c else if x = 1 then d else 0 := by
  simp only [ms, Multiset.count_add, Multiset.count_replicate]
  by_cases h1 : x = 23
  · subst h1; simp
  by_cases h2 : x = 21
  · subst h2; simp
  by_cases h3 : x = 9
  · subst h3; simp
  by_cases h4 : x = 1
  · subst h4; simp
  simp [h1, h2, h3, h4, Ne.symm h1, Ne.symm h2, Ne.symm h3, Ne.symm h4]

lemma Dp_eq : Dp = ms 1 1 3 6 := by decide

lemma count_Dp (x : ℕ) : Dp.count x =
    if x = 23 then 1 else if x = 21 then 1 else if x = 9 then 3 else if x = 1 then 6 else 0 := by
  rw [Dp_eq, count_ms]

/-- A sub-multiset of `D'` is determined by how many copies of `23, 21, 9, 1` it takes. -/
lemma sub_Dp {B : Multiset ℕ} (hB : B ≤ Dp) :
    ∃ a b c d : ℕ, a ≤ 1 ∧ b ≤ 1 ∧ c ≤ 3 ∧ d ≤ 6 ∧ B = ms a b c d := by
  have hle (x : ℕ) := Multiset.count_le_of_le x hB
  refine ⟨B.count 23, B.count 21, B.count 9, B.count 1, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [count_Dp] using hle 23
  · simpa [count_Dp] using hle 21
  · simpa [count_Dp] using hle 9
  · simpa [count_Dp] using hle 1
  · ext x
    have hx := hle x
    rw [count_Dp] at hx
    rw [count_ms]
    split_ifs at hx ⊢ <;> subst_vars <;> omega

lemma sum_ms (a b c d : ℕ) : (ms a b c d).sum = 23 * a + 21 * b + 9 * c + d := by
  simp [ms, Multiset.sum_replicate]; ring

lemma sup_replicate (n a : ℕ) : (Multiset.replicate n a).sup = if n = 0 then 0 else a := by
  induction n with
  | zero => simp
  | succ n ih => cases n <;> simp_all [Multiset.replicate_succ]

/-- When the 23 is present, the maximum is 23. -/
lemma sup_ms_one (b c d : ℕ) : (ms 1 b c d).sup = 23 := by
  simp only [ms, Multiset.sup_add, sup_replicate]
  split_ifs <;> simp_all

/-- Without 23 and 21, the maximum is 9, 1 or 0. -/
lemma sup_ms_zero (c d : ℕ) : (ms 0 0 c d).sup = if c ≠ 0 then 9 else if d ≠ 0 then 1 else 0 := by
  simp only [ms, Multiset.sup_add, sup_replicate]
  split_ifs <;> simp_all

lemma sup_ms_21 (c d : ℕ) : (ms 0 1 c d).sup = 21 := by
  simp only [ms, Multiset.sup_add, sup_replicate]
  split_ifs <;> simp_all

/-- The note's argument, for a splitting with `23 ∈ A`: `A = ms 1 (1-b) (3-c) (6-d)`, `B = ms 0 b c d`. -/
lemma key {b c d : ℕ} (hb : b ≤ 1) (hc : c ≤ 3) (hd : d ≤ 6) :
    3892 ≤ broom (ms 1 (1 - b) (3 - c) (6 - d)) (ms 0 b c d) := by
  unfold broom
  rw [sup_ms_one, sum_ms, sum_ms]
  by_contra hlt
  rw [not_le] at hlt
  have h1 := lt_of_le_of_lt (le_max_left _ _) hlt
  have h2 := lt_of_le_of_lt (le_max_right _ _) hlt
  simp only [f] at h1 h2
  push_cast at h1 h2
  -- First condition: f 23 + 53 ΣB ≤ 3891 forces ΣB = 21b + 9c + d ≤ 26.
  have hsumB : 21 * b + 9 * c + d ≤ 26 := by
    have : (53 : ℤ) * (23 * 0 + 21 * b + 9 * c + d) ≤ 1430 := by nlinarith
    omega
  -- ΣA = 77 - ΣB ≥ 51.
  have hsub : ((1 - b : ℕ) : ℤ) = 1 - b ∧ ((3 - c : ℕ) : ℤ) = 3 - c ∧ ((6 - d : ℕ) : ℤ) = 6 - d := by omega
  rw [hsub.1, hsub.2.1, hsub.2.2] at h2
  -- If the 21 is in B, max B = 21 and f 21 + 53 ΣA is already too big.
  rcases Nat.lt_or_ge b 1 with hb0 | hb1
  · have hb0 : b = 0 := by omega
    subst hb0
    rw [sup_ms_zero] at h2
    by_cases hc0 : c = 0
    · -- max B ≤ 1: B is at most six ones, but the condition needs ΣB ≥ 7.
      subst hc0
      by_cases hd0 : d = 0
      · subst hd0; simp at h2
      · simp [hd0] at h2; omega
    · -- max B = 9: the condition needs ΣB = 9c + d ∈ {25, 26}; impossible with c ≤ 3, d ≤ 6.
      simp [hc0] at h2; omega
  · have hb1 : b = 1 := by omega
    subst hb1
    rw [sup_ms_21] at h2
    push_cast at h2; omega

/-- **Lemma 3.2.** Every splitting of `D'` has value at least `3892`. -/
theorem obstruction (A B : Multiset ℕ) (h : A + B = Dp) : 3892 ≤ broom A B := by
  have h23 : (23 : ℕ) ∈ A ∨ (23 : ℕ) ∈ B := by
    have : (23 : ℕ) ∈ A + B := by rw [h]; simp [Dp]
    simpa using this
  -- By symmetry, `23 ∈ A`.
  wlog hA : (23 : ℕ) ∈ A generalizing A B
  · rw [broom_comm]; exact this B A (by rw [add_comm]; exact h) h23.symm (h23.resolve_left hA)
  have hB : B ≤ Dp := h ▸ Multiset.le_add_left B A
  obtain ⟨a, b, c, d, ha, hb, hc, hd, rfl⟩ := sub_Dp hB
  -- `A` is the complement of `B` in `D'`.
  have hAeq : A = ms (1 - a) (1 - b) (3 - c) (6 - d) := by
    ext x
    have h' := congrArg (fun s => s.count x) h
    simp only [Multiset.count_add] at h'
    rw [count_ms, count_Dp] at h'
    rw [count_ms]
    split_ifs at h' ⊢ <;> omega
  -- `23 ∈ A` means `B` does not take the single 23.
  have ha0 : a = 0 := by
    by_contra hne
    have : Multiset.count 23 A = 0 := by rw [hAeq, count_ms]; simp; omega
    exact (Multiset.count_ne_zero.mpr hA) this
  subst ha0
  rw [hAeq]; exact key hb hc hd

/-- `3892` is attained by `A = {23, 21, 1^6}`, `B = {9, 9, 9}`. -/
theorem attained : broom {23, 21, 1, 1, 1, 1, 1, 1} {9, 9, 9} = 3892 := by
  simp [broom, f]

/-- **Lemma 3.1** (arithmetic part): the three leaf values `f a + Φ(w)` of the tree `T`, and their maximum. -/
theorem leafValues :
    f 9 + (53 * (21 + 23) + (53 + 23) * 6) = 3877 ∧
    f 21 + (53 * 27 + 23 * 6) = 3858 ∧
    f 1 + (23 * (21 + 53) + (23 + 53) * 27) = 3883 := by
  simp [f]

/-- The tree `T` beats every two-branch tree with joining segment `53`: `3883 < 3892`. -/
theorem T_beats_brooms (A B : Multiset ℕ) (h : A + B = Dp) : (3883 : ℤ) < broom A B :=
  lt_of_lt_of_le (by norm_num) (obstruction A B h)

end Remoteness
