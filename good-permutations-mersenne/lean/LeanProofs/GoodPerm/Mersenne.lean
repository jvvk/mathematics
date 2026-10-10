import LeanProofs.GoodPerm.Basic

/-!
# Good permutations: only Mersenne lengths (Theorem 1, Bîsceanu) and the search reduction

* `two_adic`: in a good permutation, a block of length `2^(j+1) < n` sums to `2^j` times an odd
  number (te4's comment and Bîsceanu's answer on MO 514690);
* `congr_shift`: hence `a (t + 2^(j+1)) ≡ a t (mod 2^(j+1))`;
* `pair_gap`: if `n = q + s` with `s < q` and `a (i + q) ≡ a i (mod q)`, then
  `a (i + q) - a i = ± q`;
* `middle_sum`: under the same hypotheses the middle block `a (s+1), ..., a q` has sum
  `(q - s)(n + 1)/2`;
* `mersenne`: a good permutation of odd length `n ≥ 3` has `n = 2^m - 1`;
* `reduction`: for `n = 2^m - 1`, a good permutation has `a q = q` and `a (i + q) - a i = ± q`
  for `i < q = 2^(m-1)`: the structure the exhaustive search uses.
-/

open Finset

namespace GoodPerm

variable {n : ℕ} {a : ℕ → ℤ}

theorem two_adic (hg : Good n a) (j : ℕ) (hn : 2 ^ (j + 1) < n) (t : ℕ) (ht : 1 ≤ t)
    (hend : t + 2 ^ (j + 1) ≤ n + 1) : ∃ o : ℤ, Odd o ∧ S a t (2 ^ (j + 1)) = 2 ^ j * o := by
  induction j generalizing t with
  | zero =>
    refine ⟨S a t 2, ?_, by simp⟩
    have := hg t 2 ht le_rfl (by simpa using hn) (by simpa using hend)
    rw [← Int.not_even_iff_odd, even_iff_two_dvd]
    exact_mod_cast this
  | succ j ih =>
    have hp : 2 ^ (j + 1 + 1) = 2 ^ (j + 1) + 2 ^ (j + 1) := by rw [pow_succ]; ring
    have hn0 := hn
    have hend0 := hend
    rw [hp] at hn0 hend0
    have hc0 : 0 < 2 ^ j := Nat.two_pow_pos j
    have hjj : 2 ^ (j + 1) = 2 * 2 ^ j := by rw [pow_succ]; ring
    have hn' : 2 ^ (j + 1) < n := by omega
    obtain ⟨o1, ho1, h1⟩ := ih hn' t ht (by omega)
    obtain ⟨o2, ho2, h2⟩ := ih hn' (t + 2 ^ (j + 1)) (by omega) (by omega)
    obtain ⟨e, he⟩ := ho1.add_odd ho2
    have hsum : S a t (2 ^ (j + 1 + 1)) = 2 ^ (j + 1) * e := by
      rw [hp, S_add, h1, h2, ← mul_add, he, pow_succ]; ring
    refine ⟨e, ?_, hsum⟩
    rw [← Int.not_even_iff_odd]
    rintro ⟨f, hf⟩
    apply hg t (2 ^ (j + 1 + 1)) ht (by have := Nat.one_le_two_pow (n := j); omega) hn hend
    rw [hsum, hf]
    exact ⟨f, by push_cast; ring⟩

/-- te4's congruence `a (t + 2^(j+1)) ≡ a t (mod 2^(j+1))`. -/
theorem congr_shift (hg : Good n a) (j : ℕ) (hn : 2 ^ (j + 1) < n) (t : ℕ) (ht : 1 ≤ t)
    (hend : t + 2 ^ (j + 1) ≤ n) : (2 : ℤ) ^ (j + 1) ∣ a (t + 2 ^ (j + 1)) - a t := by
  obtain ⟨o1, ho1, h1⟩ := two_adic hg j hn t ht (by omega)
  obtain ⟨o2, ho2, h2⟩ := two_adic hg j hn (t + 1) (by omega) (by omega)
  obtain ⟨f, hf⟩ := ho2.sub_odd ho1
  have := S_shift a t (2 ^ (j + 1))
  refine ⟨f, ?_⟩
  rw [h1, h2] at this
  have e : a (t + 2 ^ (j + 1)) - a t = 2 ^ j * (o2 - o1) := by linarith
  rw [e, hf, pow_succ]; ring

section Middle

variable {q s : ℕ} (hp : IsPerm n a) (hns : n = q + s) (hsq : s < q)
  (hc : ∀ i, 1 ≤ i → i ≤ s → (q : ℤ) ∣ a (i + q) - a i)
include hp hns hsq hc

/-- Partners differ by exactly `q`. -/
theorem pair_gap (i : ℕ) (hi1 : 1 ≤ i) (his : i ≤ s) :
    a (i + q) - a i = q ∨ a (i + q) - a i = -q := by
  obtain ⟨k, hk⟩ := hc i hi1 his
  have b1 := hp.1 i hi1 (by omega)
  have b2 := hp.1 (i + q) (by omega) (by omega)
  have hne : a (i + q) ≠ a i := fun h => by
    have := hp.2 _ _ (by omega) (by omega) hi1 (by omega) h; omega
  have hq : (0 : ℤ) < q := by exact_mod_cast (by omega : 0 < q)
  have hn' : (n : ℤ) = q + s := by exact_mod_cast hns
  have hs' : (s : ℤ) < q := by exact_mod_cast hsq
  have hk1 : k < 2 := by nlinarith
  have hk2 : -2 < k := by nlinarith
  have hk0 : k ≠ 0 := by rintro rfl; apply hne; linarith
  have : k = 1 ∨ k = -1 := by omega
  rcases this with rfl | rfl
  · left; linarith
  · right; linarith

/-- The middle block `a (s + 1), ..., a q` sums to `(q - s)(n + 1)/2`. -/
theorem middle_sum : 2 * S a (s + 1) (q - s) = ((q : ℤ) - s) * (n + 1) := by
  -- the smaller member of each pair
  have hn' : (n : ℤ) = q + s := by exact_mod_cast hns
  -- positions `1..s` paired with `q+1..q+s`; write `r i` for the smaller value of the pair at `i`
  have pair : ∀ i, 1 ≤ i → i ≤ s → (a i = min (a i) (a (i + q)) ∧
      a (i + q) = min (a i) (a (i + q)) + q) ∨
      (a (i + q) = min (a i) (a (i + q)) ∧ a i = min (a i) (a (i + q)) + q) := fun i hi1 his => by
    rcases pair_gap hp hns hsq hc i hi1 his with h | h
    · left; constructor
      · rw [min_eq_left (by linarith)]
      · rw [min_eq_left (by linarith)]; linarith
    · right; constructor
      · rw [min_eq_right (by linarith)]
      · rw [min_eq_right (by linarith)]; linarith
  set m : ℕ → ℤ := fun i => min (a i) (a (i + q)) with hm
  -- `m` is a permutation of `1..s`
  have mperm : IsPerm s m := by
    refine ⟨fun i hi1 his => ?_, fun i j hi1 his hj1 hjs h => ?_⟩
    · have b1 := hp.1 i hi1 (by omega)
      have b2 := hp.1 (i + q) (by omega) (by omega)
      rcases pair i hi1 his with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp only [hm] <;> constructor <;> linarith
    · simp only [hm] at h
      rcases pair i hi1 his with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
      rcases pair j hj1 hjs with ⟨h3, h4⟩ | ⟨h3, h4⟩
      · exact hp.2 _ _ hi1 (by omega) hj1 (by omega) (by linarith)
      · have := hp.2 _ _ hi1 (by omega) (by omega) (by omega) (show a i = a (j + q) by linarith)
        omega
      · have := hp.2 _ _ (by omega) (by omega) hj1 (by omega) (show a (i + q) = a j by linarith)
        omega
      · have := hp.2 _ _ (by omega) (by omega) (by omega) (by omega)
          (show a (i + q) = a (j + q) by linarith)
        omega
  have hpair : ∀ i, 1 ≤ i → i ≤ s → a i + a (i + q) = 2 * m i + q := fun i hi1 his => by
    rcases pair i hi1 his with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp only [hm] <;> linarith
  -- total sum, split into three blocks
  have htot := perm_sum hp
  have hsplit : ∑ i ∈ range n, a (1 + i) = S a 1 s + S a (s + 1) (q - s) + S a (q + 1) s := by
    rw [show (∑ i ∈ range n, a (1 + i)) = S a 1 n from rfl,
      show n = s + (q - s) + s by omega, S_add, S_add,
      show 1 + s = s + 1 by ring, show 1 + (s + (q - s)) = q + 1 by omega]
  have houter : S a 1 s + S a (q + 1) s = 2 * ∑ i ∈ range s, m (1 + i) + s * q := by
    have e : ∀ i ∈ range s, a (1 + i) + a (q + 1 + i) = 2 * m (1 + i) + q := fun i hi => by
      simp at hi
      rw [show q + 1 + i = 1 + i + q by ring]; exact hpair (1 + i) (by omega) (by omega)
    simp only [S]
    rw [← sum_add_distrib, sum_congr rfl e, sum_add_distrib, ← mul_sum, sum_const, card_range,
      nsmul_eq_mul]
  have hm2 := two_mul_sum_id s
  have hn2 := two_mul_sum_id n
  rw [← perm_sum mperm] at hm2
  rw [← htot, hsplit] at hn2
  rw [hn']; rw [hn'] at hn2
  linear_combination hn2 - 2 * houter - 2 * hm2

end Middle

/-- Theorem 1 (Bîsceanu): a good permutation of odd length `n ≥ 3` has `n = 2^m - 1`. -/
theorem mersenne (hp : IsPerm n a) (hg : Good n a) (hodd : Odd n) (h3 : 3 ≤ n) :
    ∃ m, n = 2 ^ m - 1 := by
  set k := Nat.log 2 (n - 1) with hk
  have hk1 : 1 ≤ k := Nat.le_log_of_pow_le (by norm_num) (by omega)
  have hle : 2 ^ k ≤ n - 1 := Nat.pow_log_le_self 2 (by omega)
  have hlt : n - 1 < 2 ^ (k + 1) := Nat.lt_pow_succ_log_self (by norm_num) _
  obtain ⟨j, hj⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  set q := 2 ^ k with hq
  have hqe : Even q := by rw [hq, hj, pow_succ]; exact even_two.mul_left _
  have hn2 : n ≠ 2 * q := fun h => by
    rw [h] at hodd; exact (Nat.not_even_iff_odd.2 hodd) (even_two_mul q)
  have hqn : q < n := by omega
  have hsq : n - q < q := by rw [pow_succ] at hlt; omega
  have hc : ∀ i, 1 ≤ i → i ≤ n - q → (q : ℤ) ∣ a (i + q) - a i := fun i hi1 his => by
    have := congr_shift hg j (by rw [← hj]; exact hqn) i hi1 (by rw [← hj]; omega)
    rw [← hj] at this; exact_mod_cast this
  have hmid := middle_sum hp (by omega : n = q + (n - q)) hsq hc
  -- the middle block has length `q - s = 2q - n`; it must be a single term
  have hlen : q - (n - q) = 1 := by
    by_contra hne
    obtain ⟨h, hh⟩ := hodd
    have hdvd : ((q - (n - q) : ℕ) : ℤ) ∣ S a (n - q + 1) (q - (n - q)) := by
      refine ⟨h + 1, ?_⟩
      have : (2 : ℤ) * S a (n - q + 1) (q - (n - q)) = 2 * (((q - (n - q) : ℕ) : ℤ) * (h + 1)) := by
        have e1 : ((n - q : ℕ) : ℤ) = n - q := Nat.cast_sub hqn.le
        have e2 : ((q - (n - q) : ℕ) : ℤ) = q - ((n - q : ℕ) : ℤ) := Nat.cast_sub hsq.le
        have e3 : (n : ℤ) = 2 * h + 1 := by exact_mod_cast hh
        rw [hmid, e2, e1, e3]; ring
      linarith
    exact hg (n - q + 1) (q - (n - q)) (by omega) (by omega) (by omega) (by omega) hdvd
  exact ⟨k + 1, by rw [pow_succ]; omega⟩

/-- The search reduction: for `n = 2^m - 1`, a good permutation fixes `q = 2^(m-1)`, and the values
at positions `i` and `i + q` differ by `q`. -/
theorem reduction (m : ℕ) (hm : 2 ≤ m) (hp : IsPerm (2 ^ m - 1) a) (hg : Good (2 ^ m - 1) a) :
    a (2 ^ (m - 1)) = 2 ^ (m - 1) ∧ ∀ i, 1 ≤ i → i < 2 ^ (m - 1) →
      a (i + 2 ^ (m - 1)) - a i = 2 ^ (m - 1) ∨ a (i + 2 ^ (m - 1)) - a i = -2 ^ (m - 1) := by
  obtain ⟨j, rfl⟩ : ∃ j, m = j + 2 := ⟨m - 2, by omega⟩
  simp only [show j + 2 - 1 = j + 1 by omega]
  have hq : 2 ^ (j + 2) = 2 * 2 ^ (j + 1) := by rw [pow_succ]; ring
  have h2 : 2 ≤ 2 ^ (j + 1) := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (j + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hns : 2 ^ (j + 2) - 1 = 2 ^ (j + 1) + (2 ^ (j + 1) - 1) := by omega
  have hsq : 2 ^ (j + 1) - 1 < 2 ^ (j + 1) := by omega
  have hc : ∀ i, 1 ≤ i → i ≤ 2 ^ (j + 1) - 1 →
      ((2 ^ (j + 1) : ℕ) : ℤ) ∣ a (i + 2 ^ (j + 1)) - a i := fun i hi1 his => by
    have := congr_shift hg j (by omega) i hi1 (by omega); exact_mod_cast this
  refine ⟨?_, fun i hi1 hi => ?_⟩
  · have hmid := middle_sum hp hns hsq hc
    rw [show 2 ^ (j + 1) - (2 ^ (j + 1) - 1) = 1 by omega,
      show 2 ^ (j + 1) - 1 + 1 = 2 ^ (j + 1) by omega] at hmid
    simp only [S, range_one, sum_singleton, add_zero] at hmid
    push_cast [Nat.cast_sub (by omega : 1 ≤ 2 ^ (j + 1)), Nat.cast_sub (by omega : 1 ≤ 2 ^ (j + 2))]
      at hmid
    have : (2 : ℤ) * a (2 ^ (j + 1)) = 2 * 2 ^ (j + 1) := by rw [hmid]; ring
    exact mul_left_cancel₀ two_ne_zero this
  · have := pair_gap hp hns hsq hc i hi1 (by omega)
    push_cast at this; exact this

end GoodPerm
