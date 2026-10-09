import LeanProofs.SandorYang.Basic

/-!
# Remark 1.3 of Sándor–Yang: `A = ℕ ∖ {4^(j+2) : j ≥ 0}` (Proposition 1)

`m(N) ≤ k` where `k + 2 = ⌊log₄ N⌋` counts the admissible exponents, and `4^(k+1) ≤ N` once
`k ≥ 1`; since `3k + k² < 4^(k+1)`, the bound of `diff_ge` is positive. So `R_{A,3}` is strictly
increasing from `0`, and by `strictMono_of_three` so is every `R_{A,h}`, `h ≥ 3`.
-/

open Finset

namespace SandorYang

/-- The omitted set `{16, 64, 256, …}`. -/
def E4 : Set ℕ := {e | ∃ j, e = 4 ^ (j + 2)}

noncomputable instance : DecidablePred (· ∈ E4) := Classical.decPred _

lemma zero_not_mem_E4 : 0 ∉ E4 := by
  rintro ⟨j, hj⟩; exact absurd hj.symm (by positivity)

lemma three_k_add_sq_lt (k : ℕ) : 3 * k + k ^ 2 < 4 ^ (k + 1) := by
  induction k with
  | zero => norm_num
  | succ k ih =>
    have := Nat.lt_pow_self (by norm_num : 1 < 4) (n := k + 1)
    rw [pow_succ 4 (k + 1)]
    nlinarith

lemma m_E4_bound (N : ℕ) : 3 * m E4 N + m E4 N ^ 2 < N + 1 := by
  set k := Nat.log 4 N - 1 with hk
  -- every `4^(j+2) ≤ N` has `j < k`
  have sub : (range (N + 1)).filter (· ∈ E4) ⊆ (range k).image (fun j => 4 ^ (j + 2)) := by
    intro e he
    obtain ⟨heN, ⟨j, rfl⟩⟩ := Finset.mem_filter.1 he
    have hN : N ≠ 0 := by
      have : 0 < 4 ^ (j + 2) := by positivity
      have := Finset.mem_range.1 heN; omega
    have hl : j + 2 ≤ Nat.log 4 N :=
      Nat.le_log_of_pow_le (by norm_num) (by have := Finset.mem_range.1 heN; omega)
    exact Finset.mem_image.2 ⟨j, Finset.mem_range.2 (by omega), rfl⟩
  have hm : m E4 N ≤ k := (Finset.card_le_card sub).trans (Finset.card_image_le.trans (by simp))
  rcases Nat.eq_zero_or_pos k with h0 | hpos
  · have : m E4 N = 0 := by omega
    rw [this]; omega
  · have hN : N ≠ 0 := by
      intro h; simp [h] at hk; omega
    have hpow : 4 ^ (k + 1) ≤ N := by
      have : k + 1 = Nat.log 4 N := by omega
      rw [this]; exact Nat.pow_log_le_self 4 hN
    have := three_k_add_sq_lt k
    have : 3 * m E4 N + m E4 N ^ 2 ≤ 3 * k + k ^ 2 := by
      have := Nat.pow_le_pow_left hm 2; omega
    omega

/-- Proposition 1 for `h = 3`: `R_{A,3}` is strictly increasing from `0`. -/
theorem R3_strictMono (n : ℕ) : R E4 3 n < R E4 3 (n + 1) := by
  have h := diff_ge E4 n
  have hb := m_E4_bound (n + 1)
  have hb' : (3 * (m E4 (n + 1) : ℤ) + (m E4 (n + 1) : ℤ) ^ 2) < ((n + 1 : ℕ) : ℤ) + 1 := by
    exact_mod_cast hb
  linarith

/-- Proposition 1: for every `h ≥ 3`, `R_{A,h}(n) < R_{A,h}(n + 1)` for all `n ≥ 0`. -/
theorem R_strictMono (h : ℕ) (hh : 3 ≤ h) (n : ℕ) : R E4 h n < R E4 h (n + 1) :=
  strictMono_of_three E4 zero_not_mem_E4 R3_strictMono h hh n

end SandorYang
