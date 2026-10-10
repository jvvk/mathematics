import LeanProofs.GoodPerm.Basic

/-!
# Good permutations: the asker's construction (Theorem 2)

`c n` is `1, n - 1, n, n - 3, n - 2, ..., 2, 3`: `c n 1 = 1` and `c n t = n + 2 - t - (-1)^t` for
`t ≥ 2`. Blocks away from the first position have closed-form sums (`S_even`, `S_odd`), and so do
prefixes (`S_prefix_odd`, `S_prefix_even`).
* `interior`: no block of length `≥ 2` starting at position `≥ 2` has an integer average;
* `block_dvd_iff`: for `n = 2^m - 1`, a block of length `L ≥ 2` has an integer average exactly
  when it is a prefix and `L ∣ n`;
* `good_iff_prime`: `c n` is good iff `n` is prime;
* `c_perm`: `c n` is a permutation of `1..n` for odd `n ≥ 3`.
-/

open Finset

namespace GoodPerm

/-- The asker's permutation `1, n - 1, n, n - 3, n - 2, ..., 2, 3`. -/
def c (n t : ℕ) : ℤ := if t = 1 then 1 else (n : ℤ) + 2 - t - (-1) ^ t

lemma neg_one_pow_even_add (t r : ℕ) : (-1 : ℤ) ^ (t + 2 * r) = (-1) ^ t := by
  rw [pow_add, pow_mul]; simp

lemma neg_one_pow_odd_add (t r : ℕ) : (-1 : ℤ) ^ (t + (2 * r + 1)) = -(-1) ^ t := by
  rw [pow_add, pow_succ, pow_mul]; simp

lemma S_even (n t r : ℕ) (ht : 2 ≤ t) :
    S (c n) t (2 * r) = 2 * r * ((n : ℤ) + 2) - 2 * r * t - r * (2 * r - 1) := by
  induction r with
  | zero => simp [S]
  | succ r ih =>
    rw [show 2 * (r + 1) = 2 * r + 1 + 1 by ring]
    simp only [S] at ih ⊢
    rw [sum_range_succ, sum_range_succ, ih, c, c, ite_eq_right (by omega), ite_eq_right (by omega),
      neg_one_pow_even_add, neg_one_pow_odd_add]
    push_cast; ring

lemma S_odd (n t r : ℕ) (ht : 2 ≤ t) :
    S (c n) t (2 * r + 1) = (2 * r + 1) * ((n : ℤ) + 2 - t - r) - (-1) ^ t := by
  have := S_even n t r ht
  simp only [S] at this ⊢
  rw [sum_range_succ, this, c, ite_eq_right (by omega), neg_one_pow_even_add]
  push_cast; ring

/-- No block of length at least 2 away from the first position has an integer average. -/
theorem interior (n t L : ℕ) (ht : 2 ≤ t) (hL : 2 ≤ L) : ¬ (L : ℤ) ∣ S (c n) t L := by
  rintro ⟨k, hk⟩
  rcases Nat.even_or_odd' L with ⟨r, rfl | rfl⟩
  · rw [S_even n t r ht] at hk
    have hr : (r : ℤ) ≠ 0 := by have : 1 ≤ r := by omega
                                exact_mod_cast (by omega : r ≠ 0)
    have h2 : (r : ℤ) * (2 * r - 1) = r * (2 * ((n : ℤ) + 2 - t - k)) := by
      push_cast at hk; linear_combination -hk
    have := mul_left_cancel₀ hr h2
    omega
  · rw [S_odd n t r ht] at hk
    have hu : ((2 * r + 1 : ℕ) : ℤ) ∣ (-1) ^ t :=
      ⟨(n : ℤ) + 2 - t - r - k, by push_cast at hk ⊢; linear_combination -hk⟩
    have h1 : ((2 * r + 1 : ℕ) : ℤ) ∣ 1 := by
      rcases neg_one_pow_eq_or ℤ t with h | h <;> rw [h] at hu
      · exact hu
      · exact (dvd_neg).1 hu
    have := Int.eq_one_of_dvd_one (by positivity) h1
    omega

lemma S_prefix_odd (n r : ℕ) :
    S (c n) 1 (2 * r + 1) = (2 * r + 1) * ((n : ℤ) + 1 - r) - n := by
  rw [S_one, S_even n 2 r le_rfl, c, ite_eq_left rfl]; push_cast; ring

lemma S_prefix_even (n r : ℕ) :
    S (c n) 1 (2 * r + 2) = (2 * r + 1) * ((n : ℤ) - r) := by
  rw [S_one, S_odd n 2 r le_rfl, c, ite_eq_left rfl]; push_cast; ring

/-- An even prefix of length at most `n = 2^m - 1` never has an integer average: with
`v = 2^j u`, `u` odd, the sum `(2v - 1)(2^m - v)` is `2^j` times an odd number, and
`2v = 2^(j+1) u`. -/
lemma prefix_even_not_dvd (m r : ℕ) (hL : 2 * r + 2 ≤ 2 ^ m - 1) :
    ¬ ((2 * r + 2 : ℕ) : ℤ) ∣ S (c (2 ^ m - 1)) 1 (2 * r + 2) := by
  rw [S_prefix_even]
  obtain ⟨j, u, hu, hv⟩ := Nat.exists_eq_two_pow_mul_odd (show r + 1 ≠ 0 by omega)
  have hj : j < m := by
    have : 2 ^ j < 2 ^ m :=
      calc 2 ^ j ≤ 2 ^ j * u := Nat.le_mul_of_pos_right _ hu.pos
        _ = r + 1 := hv.symm
        _ < 2 ^ m := by omega
    exact (Nat.pow_lt_pow_iff_right (by norm_num)).1 this
  obtain ⟨k, rfl⟩ : ∃ k, m = j + k + 1 := ⟨m - j - 1, by omega⟩
  have hpow : 1 ≤ 2 ^ (j + k + 1) := Nat.one_le_two_pow
  have hr : (r : ℤ) = 2 ^ j * u - 1 := by
    have : ((r + 1 : ℕ) : ℤ) = ((2 ^ j * u : ℕ) : ℤ) := by rw [hv]
    push_cast at this; linarith
  have hS : (2 * (r : ℤ) + 1) * (((2 ^ (j + k + 1) - 1 : ℕ) : ℤ) - r)
      = 2 ^ j * ((2 * 2 ^ j * u - 1) * (2 * 2 ^ k - u)) := by
    push_cast [Nat.cast_sub hpow]; rw [hr]; ring
  have hodd : Odd ((2 * 2 ^ j * (u : ℤ) - 1) * (2 * 2 ^ k - u)) := by
    have hu' : Odd (u : ℤ) := by exact_mod_cast hu
    exact Odd.mul ⟨2 ^ j * u - 1, by ring⟩ ((even_two_mul _).sub_odd hu')
  rw [hS, show ((2 * r + 2 : ℕ) : ℤ) = 2 ^ j * (2 * u) by push_cast; rw [hr]; ring]
  intro h
  have h2 := (mul_dvd_mul_iff_left (by positivity : (2 : ℤ) ^ j ≠ 0)).1 h
  exact (Int.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 (dvd_trans (dvd_mul_right 2 _) h2))

/-- Theorem 2: for `n = 2^m - 1`, a block of length `L ≥ 2` of `c n` has an integer average exactly
when it is a prefix whose length divides `n`. -/
theorem block_dvd_iff (m t L : ℕ) (ht : 1 ≤ t) (hL : 2 ≤ L) (hend : t + L ≤ 2 ^ m - 1 + 1) :
    (L : ℤ) ∣ S (c (2 ^ m - 1)) t L ↔ t = 1 ∧ L ∣ 2 ^ m - 1 := by
  rcases Nat.lt_or_ge t 2 with h1 | h2
  · obtain rfl : t = 1 := by omega
    simp only [true_and]
    rcases Nat.even_or_odd' L with ⟨r, rfl | rfl⟩
    · obtain ⟨r, rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
      rw [show 2 * (r + 1) = 2 * r + 2 by ring]
      refine ⟨fun h => absurd h (prefix_even_not_dvd m r (by omega)), fun h => ?_⟩
      exfalso
      have hodd : Odd (2 ^ m - 1) := by
        have : 1 ≤ 2 ^ m := Nat.one_le_two_pow
        rcases m with _ | m
        · simp at hend
        · exact Nat.Even.sub_odd this (by simp [pow_succ]) odd_one
      exact (Nat.not_even_iff_odd.2 hodd) ((even_iff_two_dvd.2 (dvd_trans ⟨r + 1, by ring⟩ h)))
    · rw [S_prefix_odd, ← Int.natCast_dvd_natCast (n := 2 ^ m - 1)]
      have key : ((2 * r + 1 : ℕ) : ℤ) ∣ (2 * r + 1) * (((2 ^ m - 1 : ℕ) : ℤ) + 1 - r) := by
        rw [show ((2 * r + 1 : ℕ) : ℤ) = 2 * r + 1 by push_cast; ring]; exact dvd_mul_right _ _
      constructor
      · intro h; have := dvd_sub key h; simpa using this
      · intro h; exact dvd_sub key h
  · exact ⟨fun h => absurd h (interior _ t L h2 hL), fun h => by omega⟩

/-- Corollary: for `n = 2^m - 1 ≥ 3`, the asker's permutation is good iff `n` is prime. -/
theorem good_iff_prime (m : ℕ) (hm : 2 ≤ m) :
    Good (2 ^ m - 1) (c (2 ^ m - 1)) ↔ (2 ^ m - 1).Prime := by
  have h4 : 4 ≤ 2 ^ m := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  rw [Nat.prime_def_lt']
  constructor
  · intro hg
    refine ⟨by omega, fun d hd2 hdn hd => ?_⟩
    exact hg 1 d le_rfl hd2 hdn (by omega)
      ((block_dvd_iff m 1 d le_rfl hd2 (by omega)).2 ⟨rfl, hd⟩)
  · rintro ⟨_, hp⟩ t L ht hL hLn hend hdvd
    obtain ⟨-, hd⟩ := (block_dvd_iff m t L ht hL hend).1 hdvd
    exact hp L hL hLn hd

/-- The asker's sequence is a permutation of `1..n` for odd `n ≥ 3`. -/
theorem c_perm (n : ℕ) (hn : Odd n) : IsPerm n (c n) := by
  obtain ⟨k, rfl⟩ := hn
  have val : ∀ t, 2 ≤ t → (Even t → c (2 * k + 1) t = 2 * k + 2 - t) ∧
      (Odd t → c (2 * k + 1) t = 2 * k + 4 - t) := fun t ht => by
    refine ⟨fun he => ?_, fun ho => ?_⟩ <;> rw [c, ite_eq_right (by omega)]
    · rw [he.neg_one_pow]; push_cast; ring
    · rw [ho.neg_one_pow]; push_cast; ring
  refine ⟨fun t ht1 htn => ?_, fun s t hs1 hsn ht1 htn h => ?_⟩
  · rcases Nat.lt_or_ge t 2 with h1 | h2
    · obtain rfl : t = 1 := by omega
      simp [c]
    · rcases Nat.even_or_odd t with he | ho
      · rw [(val t h2).1 he]
        obtain ⟨j, rfl⟩ := he
        constructor <;> push_cast <;> omega
      · rw [(val t h2).2 ho]
        obtain ⟨j, rfl⟩ := ho
        constructor <;> push_cast <;> omega
  · have key : ∀ u, 1 ≤ u → u ≤ 2 * k + 1 → (u = 1 ∧ c (2 * k + 1) u = 1) ∨
        (2 ≤ u ∧ Even u ∧ c (2 * k + 1) u = 2 * k + 2 - u) ∨
        (2 ≤ u ∧ Odd u ∧ c (2 * k + 1) u = 2 * k + 4 - u) := fun u hu1 hun => by
      rcases Nat.lt_or_ge u 2 with h1 | h2
      · left; obtain rfl : u = 1 := by omega
        simp [c]
      · rcases Nat.even_or_odd u with he | ho
        · exact Or.inr (Or.inl ⟨h2, he, (val u h2).1 he⟩)
        · exact Or.inr (Or.inr ⟨h2, ho, (val u h2).2 ho⟩)
    rcases key s hs1 hsn with ⟨a1, b1⟩ | ⟨a1, ⟨j1, hj1⟩, b1⟩ | ⟨a1, ⟨j1, hj1⟩, b1⟩ <;>
    rcases key t ht1 htn with ⟨a2, b2⟩ | ⟨a2, ⟨j2, hj2⟩, b2⟩ | ⟨a2, ⟨j2, hj2⟩, b2⟩ <;>
    rw [b1, b2] at h <;> push_cast at h <;> omega

end GoodPerm
