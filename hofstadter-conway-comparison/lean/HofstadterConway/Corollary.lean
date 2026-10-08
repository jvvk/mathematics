/-
  Lemma 2.1 (the two forms of symmetry) and the by-products of Corollary 4.2:
  `c(2^k) = s(2^k) = 2^(k-1)`, `s` is slow, and `s(n) - n/2` has sign `(-1)^k` or vanishes on
  `[2^k, 2^(k+1)]`.
-/
import HofstadterConway.Main

namespace HofConway

/-- **Lemma 2.1**: for a Dyck word, the prefix form of symmetry is equivalent to the letter form
`u_(L+1-i) = 1 - u_i`. -/
theorem symm_iff_letter {L : ℕ} {P : ℕ → ℕ} (hD : Dyck L P) :
    Symm L P ↔ ∀ i, 1 ≤ i → i ≤ L → letter P (L + 1 - i) + letter P i = 1 := by
  constructor
  · intro hS i h1 h2
    have e1 := hS i h2
    have e2 := hS (i - 1) (by omega)
    have s1 := hD.step (i - 1)
    have s2 := hD.step (L - i)
    unfold letter
    rw [show L - (i - 1) = L + 1 - i by omega] at e2
    rw [show i - 1 + 1 = i by omega] at s1
    rw [show L - i + 1 = L + 1 - i by omega] at s2
    rw [show L + 1 - i - 1 = L - i by omega]
    omega
  · intro hl i hi
    induction i with
    | zero => have := hD.total; simp only [Nat.sub_zero, hD.zero]; omega
    | succ i ih =>
      have e := ih (by omega)
      have h := hl (i + 1) (by omega) hi
      unfold letter at h
      rw [show L + 1 - (i + 1) = L - i by omega, show L - i - 1 = L - (i + 1) by omega,
        show i + 1 - 1 = i by omega] at h
      have s1 := hD.step i
      have s2 := hD.step (L - (i + 1))
      rw [show L - (i + 1) + 1 = L - i by omega] at s2
      omega

theorem half_pow (k : ℕ) (hk : 1 ≤ k) : 2 ^ k / 2 = 2 ^ (k - 1) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [pow_succ]; simp

/-- **Corollary 4.2**: `c(2^k) = s(2^k) = 2^(k-1)`. -/
theorem c_s_pow (k : ℕ) (hk : 1 ≤ k) : c (2 ^ k) = 2 ^ (k - 1) ∧ s (2 ^ k) = 2 ^ (k - 1) := by
  obtain ⟨hc, hs⟩ := blocks k hk 0 (Nat.zero_le _)
  have hv := v_dyck k hk
  have hw := (w_props k hk).1
  rw [add_zero, hw.zero, add_zero] at hc
  rw [add_zero] at hs
  unfold sForm at hs
  rw [hv.zero] at hs
  rw [← half_pow k hk]
  split_ifs at hs <;> omega

/-- Block position of `n ≥ 2`. -/
theorem block_of (n : ℕ) (h : 2 ≤ n) :
    ∃ k, 1 ≤ k ∧ 2 ^ k ≤ n ∧ n < 2 * 2 ^ k := by
  refine ⟨Nat.log 2 n, Nat.log_pos (by norm_num) h, Nat.pow_log_le_self 2 (by omega), ?_⟩
  have := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) n
  rwa [two_pow_succ] at this

/-- **Corollary 4.2**: `s` is slow, its increments are `0` or `1`. -/
theorem s_slow (n : ℕ) (hn : 1 ≤ n) : s n ≤ s (n + 1) ∧ s (n + 1) ≤ s n + 1 := by
  rcases Nat.lt_or_ge n 2 with h | h
  · obtain rfl : n = 1 := by omega
    rw [s_one, s_two]; omega
  obtain ⟨k, hk, hlo, hhi⟩ := block_of n h
  have hv := v_dyck k hk
  set t := n - 2 ^ k with ht
  obtain ⟨-, hs0⟩ := blocks k hk t (by omega)
  obtain ⟨-, hs1⟩ := blocks k hk (t + 1) (by omega)
  rw [show 2 ^ k + t = n by omega] at hs0
  rw [show 2 ^ k + (t + 1) = n + 1 by omega] at hs1
  have st := hv.step t
  have l0 := hv.le_self t
  have l1 := hv.le_self (t + 1)
  unfold sForm at hs0 hs1
  split_ifs at hs0 hs1 <;> omega

/-- **Corollary 4.2**: on `[2^k, 2^(k+1)]`, `s(n) - n/2 ≥ 0` for even `k` and `≤ 0` for odd `k`. -/
theorem s_sign (k : ℕ) (hk : 1 ≤ k) (n : ℕ) (h1 : 2 ^ k ≤ n) (h2 : n ≤ 2 ^ (k + 1)) :
    (k % 2 = 0 → n ≤ 2 * s n) ∧ (k % 2 = 1 → 2 * s n ≤ n) := by
  rw [two_pow_succ] at h2
  have hv := v_dyck k hk
  set t := n - 2 ^ k with ht
  obtain ⟨-, hs⟩ := blocks k hk t (by omega)
  rw [show 2 ^ k + t = n by omega] at hs
  have hh := hv.half t (by omega)
  have hl := hv.le_self t
  have he : 2 * (2 ^ k / 2) = 2 ^ k := by rw [half_pow k hk, ← pow_succ']; congr 1; omega
  unfold sForm at hs
  constructor <;> intro hk2 <;> split_ifs at hs <;> omega

end HofConway
