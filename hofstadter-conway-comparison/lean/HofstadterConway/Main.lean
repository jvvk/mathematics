/-
  Proof of Theorem 1.1 (Section 5 of the paper): for every `n ≥ 1`,
  `|s(n) - n/2| ≤ c(n) - n/2`, equivalently `n - c(n) ≤ s(n) ≤ c(n)`.
-/
import HofstadterConway.Blocks

namespace HofConway

/-- The base case of Section 5: `v_3 = 𝓣(w_3)` (both are `11010100`). -/
theorem base_three : ∀ i, i ≤ 8 → vP 3 i = TP 8 (wP 3) i := by decide

/-- The two-step induction of Section 5: `v_k ≤ 𝓣(w_k)` gives `v_{k+2} ≤ 𝓣(w_{k+2})` for odd `k`. -/
theorem odd_step {k : ℕ} (hk : 3 ≤ k) (hodd : k % 2 = 1)
    (h : ∀ i, vP k i ≤ TP (2 ^ k) (wP k) i) :
    ∀ i, vP (k + 2) i ≤ TP (2 ^ (k + 2)) (wP (k + 2)) i := by
  intro i
  have hk1 : 1 ≤ k := by omega
  have hw := w_props k hk1
  have hv := v_dyck k hk1
  have h4 : 4 ≤ 2 ^ k := Nat.le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) (by omega : 2 ≤ k))
  have hT := TP_dyck hw.1 hw.2.1 hw.2.2 h4
  show vP (k + 1 + 1) i ≤ TP (2 ^ (k + 1 + 1)) (wP (k + 1 + 1)) i
  rw [vP_succ_even (by omega) (by omega), vP_succ_odd hk1 hodd, wP_succ (by omega), wP_succ hk1,
    show 2 ^ (k + 1 + 1) = 2 * (2 * 2 ^ k) by ring, show 2 ^ (k + 1) = 2 * 2 ^ k by ring]
  have m1 := FP_mono hv hT h
  have m2 := GP_mono (FP_dyck hv) (FP_dyck hT) m1 i
  exact le_trans m2 (key hw.1 hw.2.1 hw.2.2 h4 i)

/-- `v_k ≤ 𝓣(w_k)` for every odd `k ≥ 3`, written `k = 2n + 3`. -/
theorem odd_blocks (n : ℕ) : ∀ i, vP (2 * n + 3) i ≤ TP (2 ^ (2 * n + 3)) (wP (2 * n + 3)) i := by
  induction n with
  | zero =>
    intro i
    have hv := v_dyck 3 (by norm_num)
    have hw := w_props 3 (by norm_num)
    have hT := TP_dyck hw.1 hw.2.1 hw.2.2 (by norm_num)
    simp only [show (2 : ℕ) ^ 3 = 8 by norm_num] at hv hT ⊢
    rcases le_total i 8 with h | h
    · exact le_of_eq (base_three i h)
    · rw [hv.tail i h, hT.tail i h]; exact le_of_eq (base_three 8 le_rfl)
  | succ n ih =>
    rw [show 2 * (n + 1) + 3 = 2 * n + 3 + 2 by omega]
    exact odd_step (by omega) (by omega) ih

/-- Corollary 4.2's reduction: `v_k ≤ w_k` for every `k ≥ 1`. -/
theorem v_le_w (k : ℕ) (hk : 1 ≤ k) (i : ℕ) : vP k i ≤ wP k i := by
  obtain ⟨n, rfl | rfl | rfl | rfl⟩ : ∃ n, k = 1 ∨ k = 2 ∨ k = 2 * n + 3 ∨ k = 2 * n + 4 :=
    ⟨(k - 3) / 2, by omega⟩
  · exact le_rfl
  · exact le_rfl
  · have hw := w_props (2 * n + 3) (by omega)
    exact le_trans (odd_blocks n i) (TP_le hw.1 (Nat.le_trans (by norm_num)
      (Nat.pow_le_pow_right (by norm_num) (by omega : 2 ≤ 2 * n + 3))) i)
  · have k1 : 1 ≤ 2 * n + 3 := by omega
    have hw := w_props (2 * n + 3) k1
    have hv := v_dyck (2 * n + 3) k1
    have h4 : 4 ≤ 2 ^ (2 * n + 3) := Nat.le_trans (by norm_num)
      (Nat.pow_le_pow_right (by norm_num) (by omega : 2 ≤ 2 * n + 3))
    have hT := TP_dyck hw.1 hw.2.1 hw.2.2 h4
    rw [show 2 * n + 4 = 2 * n + 3 + 1 by omega, vP_succ_odd k1 (by omega), wP_succ k1]
    exact le_trans (FP_mono hv hT (odd_blocks n) i) (FP_mono hT hw.1 (TP_le hw.1 h4) i)

/-- **Theorem 1.1** (natural-number form): `n - c(n) ≤ s(n) ≤ c(n)` for every `n ≥ 1`. -/
theorem main (n : ℕ) (hn : 1 ≤ n) : n ≤ c n + s n ∧ s n ≤ c n := by
  rcases Nat.lt_or_ge n 2 with h | h
  · have : n = 1 := by omega
    subst this; rw [c_one, s_one]; omega
  set k := Nat.log 2 n with hkdef
  have hk1 : 1 ≤ k := Nat.log_pos (by norm_num) h
  have hlo : 2 ^ k ≤ n := Nat.pow_log_le_self 2 (by omega)
  have hhi : n < 2 ^ (k + 1) := Nat.lt_pow_succ_log_self (by norm_num) n
  rw [two_pow_succ] at hhi
  have hv := v_dyck k hk1
  have hw := (w_props k hk1).1
  have hE := hw.total
  have ht : n - 2 ^ k ≤ 2 ^ k := by omega
  obtain ⟨hc, hs⟩ := blocks k hk1 (n - 2 ^ k) ht
  rw [show 2 ^ k + (n - 2 ^ k) = n by omega] at hc hs
  have hvw := v_le_w k hk1 (n - 2 ^ k)
  have hhalf := hv.half (n - 2 ^ k) ht
  have hvl := hv.le_self (n - 2 ^ k)
  unfold sForm at hs
  split_ifs at hs <;> omega

/-- **Theorem 1.1**: `|s(n) - n/2| ≤ c(n) - n/2` for every `n ≥ 1`. -/
theorem hofstadter_conway_dominates (n : ℕ) (hn : 1 ≤ n) :
    |(s n : ℚ) - n / 2| ≤ c n - n / 2 := by
  obtain ⟨h1, h2⟩ := main n hn
  have h1' : (n : ℚ) ≤ c n + s n := by exact_mod_cast h1
  have h2' : (s n : ℚ) ≤ c n := by exact_mod_cast h2
  rw [abs_le]; constructor <;> linarith

/-! ### Faithfulness: the Lean `c` and `s` are the sequences of the paper -/

/-- `1 ≤ c m ≤ m` and `1 ≤ s m ≤ m` for `m ≥ 1`. -/
theorem bounds (m : ℕ) (hm : 1 ≤ m) : 1 ≤ c m ∧ c m ≤ m ∧ 1 ≤ s m ∧ s m ≤ m := by
  rcases Nat.lt_or_ge m 2 with h | h
  · have : m = 1 := by omega
    subst this; rw [c_one, s_one]; omega
  set k := Nat.log 2 m
  have hk1 : 1 ≤ k := Nat.log_pos (by norm_num) h
  have hlo : 2 ^ k ≤ m := Nat.pow_log_le_self 2 (by omega)
  have hhi : m < 2 ^ (k + 1) := Nat.lt_pow_succ_log_self (by norm_num) m
  rw [two_pow_succ] at hhi
  have hv := v_dyck k hk1
  have hw := (w_props k hk1).1
  have hE := hw.total
  have h2 : 2 ≤ 2 ^ k := Nat.le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hk1)
  have ht : m - 2 ^ k ≤ 2 ^ k := by omega
  obtain ⟨hc, hs⟩ := blocks k hk1 (m - 2 ^ k) ht
  rw [show 2 ^ k + (m - 2 ^ k) = m by omega] at hc hs
  have := hw.le_self (m - 2 ^ k)
  have := hv.le_self (m - 2 ^ k)
  unfold sForm at hs
  split_ifs at hs <;> omega

/-- The Lean `c` satisfies the Hofstadter–Conway recurrence with every argument in `[1, n-1]`. -/
theorem c_recurrence (n : ℕ) (hn : 3 ≤ n) :
    1 ≤ c (n - 1) ∧ c (n - 1) ≤ n - 1 ∧ c n = c (c (n - 1)) + c (n - c (n - 1)) := by
  obtain ⟨h1, h2, -, -⟩ := bounds (n - 1) (by omega)
  exact ⟨h1, h2, by rw [c_rec hn, if_pos ⟨h1, h2⟩]⟩

/-- The Lean `s` satisfies Alkan's recurrence exactly, over `ℤ`, with every argument in `[1, n-1]`. -/
theorem s_recurrence (n : ℕ) (hn : 3 ≤ n) :
    1 ≤ s (n - 1) ∧ s (n - 1) ≤ n - 1 ∧
      (s n : ℤ) = n - s (s (n - 1)) - s (n - s (n - 1)) := by
  obtain ⟨-, -, h1, h2⟩ := bounds (n - 1) (by omega)
  refine ⟨h1, h2, ?_⟩
  have hsn := (bounds n (by omega)).2.2.1
  have e : s n = n - s (s (n - 1)) - s (n - s (n - 1)) := by rw [s_rec hn, if_pos ⟨h1, h2⟩]
  -- the truncated subtraction does not truncate, since `s n ≥ 1`
  have : s (s (n - 1)) + s (n - s (n - 1)) < n := by omega
  omega

end HofConway
