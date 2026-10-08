import MexSequence.Basic

/-!
  The paper's proof of unboundedness (Lemmas 1 and 2), which never uses the exact values.
  For any mex sequence `a` started from `1,1,1,0,1,0,1,1`:
  * `zeros`: apart from `a 0 = 1`, the zeros are exactly the positions `≡ 0, 3 (mod 5)`;
  * `twins`: `a (5b+1) = a (5b+2)` for every block `b`, and for `b ≥ 2` this value differs from
    every earlier `a (5c+1)`, because a zero copies each earlier twin into the set of sums.
  Infinitely many distinct values cannot be bounded (`unbounded_of_twins`).
-/

namespace MexE27

variable {a : ℕ → ℕ}

theorem mex_zero_iff (S : Finset ℕ) : mex S = 0 ↔ 0 ∉ S := by
  rw [mex_eq_iff]; simp

theorem rec_spec (ha : IsMex a) (n : ℕ) (hn : 7 ≤ n) :
    a (n + 1) ∉ sums a n ∧ ∀ u < a (n + 1), u ∈ sums a n := by
  rw [← mex_eq_iff]; exact (ha.2.2.2.2.2.2.2.2 n hn).symm

/-- Lemma 1: apart from `a 0 = 1`, the zeros are exactly at the positions `≡ 0, 3 (mod 5)`. -/
theorem zeros (ha : IsMex a) : ∀ m, a m = 0 ↔ m ≠ 0 ∧ (m % 5 = 0 ∨ m % 5 = 3) := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, hr⟩ := id ha
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    rcases Nat.lt_or_ge m 8 with hm | hm
    · interval_cases m <;> simp [h0, h1, h2, h3, h4, h5, h6, h7]
    · obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
      have hz : a (n + 1) = 0 ↔ 0 ∉ sums a n := by
        rw [hr n (by omega)]; exact mex_zero_iff _
      rw [hz, mem_sums]
      constructor
      · intro hno
        by_contra hcon
        apply hno
        rcases (by omega : (n + 1) % 5 = 1 ∨ (n + 1) % 5 = 2 ∨ (n + 1) % 5 = 4) with h | h | h
        · -- two zeros at 5 and n - 5
          have := (ih (n - 5) (by omega)).2 ⟨by omega, by omega⟩
          exact ⟨5, by omega, by omega⟩
        · -- two zeros at 3 and n - 3
          have := (ih (n - 3) (by omega)).2 ⟨by omega, by omega⟩
          exact ⟨3, by omega, by omega⟩
        · have := (ih (n - 3) (by omega)).2 ⟨by omega, by omega⟩
          exact ⟨3, by omega, by omega⟩
      · rintro ⟨-, hmod⟩ ⟨i, hi, hs⟩
        have hi0 := (ih i (by omega)).1 (by omega)
        have hj0 := (ih (n - i) (by omega)).1 (by omega)
        omega

/-- Lemma 2: the two twin positions of every block agree, and from block `2` on each new twin
    value differs from every earlier one. -/
theorem twins (ha : IsMex a) :
    ∀ b, a (5 * b + 1) = a (5 * b + 2) ∧ (2 ≤ b → ∀ c < b, a (5 * b + 1) ≠ a (5 * c + 1)) := by
  obtain ⟨h0, h1, h2, -, -, -, h6, h7, -⟩ := id ha
  have Z := zeros ha
  have hz : ∀ k, k ≠ 0 → (k % 5 = 0 ∨ k % 5 = 3) → a k = 0 := fun k h1 h2 => (Z k).2 ⟨h1, h2⟩
  have hnz : ∀ k, (k % 5 = 1 ∨ k % 5 = 2 ∨ k % 5 = 4) → a k ≠ 0 := fun k hk h => by
    have := (Z k).1 h; omega
  intro b
  induction b using Nat.strong_induction_on with
  | _ b ih =>
    rcases Nat.lt_or_ge b 2 with hb | hb
    · interval_cases b
      · exact ⟨by simp [h1, h2], by omega⟩
      · exact ⟨by simp [h6, h7], by omega⟩
    -- earlier twins agree
    have tw : ∀ k, k < 5 * b → k % 5 = 1 → a (k + 1) = a k := fun k hk hk1 => by
      have := (ih (k / 5) (by omega)).1
      rw [show 5 * (k / 5) + 1 = k by omega, show 5 * (k / 5) + 2 = k + 1 by omega] at this
      exact this.symm
    obtain ⟨hnot, hcov⟩ := rec_spec ha (5 * b) (by omega)
    -- copying: every earlier twin value is a sum `a (5c+2) + 0` for the index sum `5b`
    have hd : ∀ c < b, a (5 * b + 1) ≠ a (5 * c + 1) := fun c hc heq => by
      apply hnot
      rw [mem_sums]
      have hzero := hz (5 * b - (5 * c + 2)) (by omega) (by omega)
      have htw := (ih c hc).1
      exact ⟨5 * c + 2, by omega, by omega⟩
    have hd' : ∀ k, k < 5 * b → k % 5 = 1 → a k ≠ a (5 * b + 1) := fun k hk hk1 heq => by
      have := hd (k / 5) (by omega)
      rw [show 5 * (k / 5) + 1 = k by omega] at this
      exact this heq.symm
    have hv : a (5 * b + 1) ≠ 0 := hnz _ (by omega)
    refine ⟨?_, fun _ => hd⟩
    obtain ⟨-, -, -, -, -, -, -, -, hr⟩ := id ha
    rw [hr (5 * b + 1) (by omega)]
    symm
    rw [mex_eq_iff, mem_sums]
    constructor
    · -- the new value is not a sum for the index sum `5b+1`
      rintro ⟨i, hi, hs⟩
      have hcase : i = 0 ∨ i = 5 * b + 1 ∨ (i ≠ 0 ∧ i % 5 = 0) ∨ (i ≠ 5 * b + 1 ∧ i % 5 = 1) ∨
          i % 5 = 2 ∨ i % 5 = 3 ∨ i % 5 = 4 := by omega
      rcases hcase with rfl | rfl | ⟨hi0, hi5⟩ | ⟨hi0, hi5⟩ | hi5 | hi5 | hi5
      · rw [h0, Nat.sub_zero] at hs; omega
      · rw [Nat.sub_self, h0] at hs; omega
      · -- a zero copies the twin at `5b+1-i`, an earlier one
        have := hz i hi0 (by omega)
        exact hd' (5 * b + 1 - i) (by omega) (by omega) (by omega)
      · have := hz (5 * b + 1 - i) (by omega) (by omega)
        exact hd' i (by omega) (by omega) (by omega)
      · -- the mixed sum also occurs for the index sum `5b`, via the equal first twin
        have := tw (i - 1) (by omega) (by omega)
        rw [show i - 1 + 1 = i by omega] at this
        apply hnot
        rw [mem_sums]
        exact ⟨i - 1, by omega, by rw [show 5 * b - (i - 1) = 5 * b + 1 - i by omega]; omega⟩
      · have := hz i (by omega) (by omega)
        have := hz (5 * b + 1 - i) (by omega) (by omega)
        omega
      · have := tw (5 * b + 1 - i - 1) (by omega) (by omega)
        apply hnot
        rw [mem_sums]
        exact ⟨i, by omega, by
          rw [show 5 * b - i = 5 * b + 1 - i - 1 by omega,
            show 5 * b + 1 - i - 1 + 1 = 5 * b + 1 - i by omega] at *; omega⟩
    · -- every smaller value is a sum for `5b`, and each such sum recurs for `5b+1`
      intro u hu
      refine (mem_sums _ _ _).2 ?_
      obtain ⟨i, hi, hs⟩ := (mem_sums a (5 * b) u).1 (hcov u hu)
      have hcase : i = 0 ∨ i = 5 * b ∨ (i ≠ 0 ∧ i ≠ 5 * b ∧ i % 5 = 0) ∨ i % 5 = 1 ∨
          i % 5 = 2 ∨ i % 5 = 3 ∨ i % 5 = 4 := by omega
      rcases hcase with rfl | rfl | ⟨hi0, hib, hi5⟩ | hi5 | hi5 | hi5 | hi5
      · -- `1 + 0`
        have := hz (5 * b) (by omega) (by omega)
        simp only [h0, Nat.sub_zero] at hs
        exact ⟨1, by omega, by rw [show 5 * b + 1 - 1 = 5 * b by omega, h1]; omega⟩
      · have := hz (5 * b) (by omega) (by omega)
        simp only [h0, Nat.sub_self] at hs
        exact ⟨1, by omega, by rw [show 5 * b + 1 - 1 = 5 * b by omega, h1]; omega⟩
      · -- `0 + 0`
        have := hz i hi0 (by omega)
        have := hz (5 * b - i) (by omega) (by omega)
        have := hz (5 * b - 2) (by omega) (by omega)
        have h3 := ha.2.2.2.1
        exact ⟨3, by omega, by rw [show 5 * b + 1 - 3 = 5 * b - 2 by omega]; omega⟩
      · have := tw i (by omega) hi5
        exact ⟨i + 1, by omega, by rw [show 5 * b + 1 - (i + 1) = 5 * b - i by omega]; omega⟩
      · have := hz (5 * b - i) (by omega) (by omega)
        have := tw (i - 1) (by omega) (by omega)
        have := hz (5 * b + 1 - (i - 1)) (by omega) (by omega)
        exact ⟨i - 1, by omega, by rw [show i - 1 + 1 = i by omega] at *; omega⟩
      · have := hz i (by omega) (by omega)
        have := tw (5 * b - i - 1) (by omega) (by omega)
        have := hz (5 * b + 1 - (5 * b - i - 1)) (by omega) (by omega)
        exact ⟨5 * b - i - 1, by omega, by
          rw [show 5 * b - i - 1 + 1 = 5 * b - i by omega] at *; omega⟩
      · have := tw (5 * b - i) (by omega) (by omega)
        exact ⟨i, by omega, by rw [show 5 * b + 1 - i = 5 * b - i + 1 by omega]; omega⟩

/-- Theorem 1 by the paper's route: the twin values `a (5b+1)`, `b ≥ 2`, are pairwise distinct,
    so the sequence is unbounded. -/
theorem unbounded_of_twins (ha : IsMex a) : ∀ M, ∃ n, M ≤ a n := by
  intro M
  by_contra h
  push Not at h
  obtain ⟨x, -, y, -, hne, heq⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to
    (s := Finset.range (M + 1)) (t := Finset.range M) (f := fun b => a (5 * (b + 2) + 1))
    (by simp) (by intro b _; simpa using h _)
  have heq' : a (5 * (x + 2) + 1) = a (5 * (y + 2) + 1) := heq
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · exact (twins ha (y + 2)).2 (by omega) (x + 2) (by omega) heq'.symm
  · exact (twins ha (x + 2)).2 (by omega) (y + 2) (by omega) heq'

theorem not_eventually_periodic_of_twins (ha : IsMex a) :
    ¬ ∃ p N, 0 < p ∧ ∀ n, N ≤ n → a (n + p) = a n := by
  rintro ⟨p, N, hp, hper⟩
  have hbound : ∀ n, a n ≤ (Finset.range (N + p)).sup a := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      rcases Nat.lt_or_ge n (N + p) with h | h
      · exact Finset.le_sup (f := a) (Finset.mem_range.2 h)
      · have := hper (n - p) (by omega)
        rw [show n - p + p = n by omega] at this
        rw [this]; exact ih _ (by omega)
  obtain ⟨n, hn⟩ := unbounded_of_twins ha ((Finset.range (N + p)).sup a + 1)
  have := hbound n
  omega

end MexE27
