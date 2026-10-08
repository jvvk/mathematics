/-
  The block words of `c` and `s` (Section 4 of the paper: Proposition 4.1, Lemma 4.3).

  `wP k`, `vP k` are the prefix counts of `w_k`, `v_k` (length `2^k`). We show that the Lean
  functions `c` and `s` follow formula (4.1) on every block `[2^k, 2^{k+1}]`; in particular every
  recursive call in their definitions stays inside `[1, n-1]`, so `s` is well defined.
-/
import HofstadterConway.Key

namespace HofConway

theorem c_rec {n : ℕ} (h : 3 ≤ n) :
    c n = if 1 ≤ c (n - 1) ∧ c (n - 1) ≤ n - 1 then c (c (n - 1)) + c (n - c (n - 1)) else 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  rw [c]; simp only [show m + 3 - 1 = m + 2 by omega]; rfl

theorem s_rec {n : ℕ} (h : 3 ≤ n) :
    s n = if 1 ≤ s (n - 1) ∧ s (n - 1) ≤ n - 1 then n - s (s (n - 1)) - s (n - s (n - 1))
      else 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  rw [s]; simp only [show m + 3 - 1 = m + 2 by omega]; rfl

theorem c_step {n x : ℕ} (h3 : 3 ≤ n) (hx : c (n - 1) = x) (h1 : 1 ≤ x) (h2 : x ≤ n - 1) :
    c n = c x + c (n - x) := by
  rw [c_rec h3, hx, if_pos ⟨h1, h2⟩]

theorem s_step {n x : ℕ} (h3 : 3 ≤ n) (hx : s (n - 1) = x) (h1 : 1 ≤ x) (h2 : x ≤ n - 1) :
    s n = n - s x - s (n - x) := by
  rw [s_rec h3, hx, if_pos ⟨h1, h2⟩]

theorem c_one : c 1 = 1 := by rw [c]
theorem c_two : c 2 = 1 := by rw [c]
theorem s_one : s 1 = 1 := by rw [s]
theorem s_two : s 2 = 1 := by rw [s]
theorem c_three : c 3 = 2 := by rw [c_step (x := 1) le_rfl c_two le_rfl (by norm_num), c_one, c_two]
theorem c_four : c 4 = 2 := by
  rw [c_step (x := 2) (by norm_num) c_three (by norm_num) (by norm_num), c_two]
theorem s_three : s 3 = 1 := by rw [s_step (x := 1) le_rfl s_two le_rfl (by norm_num), s_one, s_two]
theorem s_four : s 4 = 2 := by
  rw [s_step (x := 1) (by norm_num) s_three le_rfl (by norm_num), s_one, s_three]

/-! ### The first block and the block words -/

/-- Prefix counts of the word `10`. -/
def P10 (i : ℕ) : ℕ := min i 1

theorem P10_dyck : Dyck 2 P10 where
  zero := by simp [P10]
  step i := by unfold P10; omega
  tail i _ := by unfold P10; omega
  half i _ := by unfold P10; omega
  total := by unfold P10; omega

theorem P10_irred : Irred 2 P10 := by intro i _ _; unfold P10; omega

theorem P10_symm : Symm 2 P10 := by intro i _; unfold P10; omega

/-- `w_k`: `w_1 = 10`, `w_{k+1} = 𝓕(w_k)` (index `0` is unused). -/
def wP : ℕ → ℕ → ℕ
  | 0 => P10
  | 1 => P10
  | k + 2 => FP (2 ^ (k + 1)) (wP (k + 1))

/-- `v_k`: `v_1 = 10`, `v_{k+1} = 𝓕(v_k)` for odd `k` and `𝓖(v_k)` for even `k`. -/
def vP : ℕ → ℕ → ℕ
  | 0 => P10
  | 1 => P10
  | k + 2 => if (k + 1) % 2 = 1 then FP (2 ^ (k + 1)) (vP (k + 1)) else GP (2 ^ (k + 1)) (vP (k + 1))

theorem wP_succ {k : ℕ} (hk : 1 ≤ k) : wP (k + 1) = FP (2 ^ k) (wP k) := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩; rfl

theorem vP_succ_odd {k : ℕ} (hk : 1 ≤ k) (h : k % 2 = 1) : vP (k + 1) = FP (2 ^ k) (vP k) := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  show (if (k' + 1) % 2 = 1 then _ else _) = _; rw [if_pos h]

theorem vP_succ_even {k : ℕ} (hk : 1 ≤ k) (h : k % 2 = 0) : vP (k + 1) = GP (2 ^ k) (vP k) := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  show (if (k' + 1) % 2 = 1 then _ else _) = _; rw [if_neg (by omega)]

theorem two_pow_succ (k : ℕ) : 2 ^ (k + 1) = 2 * 2 ^ k := by ring

/-- Lemma 4.3 for `w_k`, with Dyck-ness: every `w_k` is a symmetric irreducible Dyck word. -/
theorem w_props : ∀ k, 1 ≤ k → Dyck (2 ^ k) (wP k) ∧ Irred (2 ^ k) (wP k) ∧ Symm (2 ^ k) (wP k) := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => exact ⟨P10_dyck, P10_irred, P10_symm⟩
  | succ k hk ih =>
    rw [wP_succ hk, two_pow_succ]
    obtain ⟨h1, h2, h3⟩ := ih
    exact ⟨FP_dyck h1, FP_irred h1 h2, FP_symm h1 h3⟩

/-- Every `v_k` is a Dyck word (Lemma 2.2(4)). -/
theorem v_dyck : ∀ k, 1 ≤ k → Dyck (2 ^ k) (vP k) := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => exact P10_dyck
  | succ k hk ih =>
    rw [two_pow_succ]
    rcases Nat.mod_two_eq_zero_or_one k with h | h
    · rw [vP_succ_even hk h]; exact GP_dyck ih
    · rw [vP_succ_odd hk h]; exact FP_dyck ih

/-- Every `v_k` is symmetric (Lemma 4.3). -/
theorem v_symm : ∀ k, 1 ≤ k → Symm (2 ^ k) (vP k) := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => exact P10_symm
  | succ k hk ih =>
    rw [two_pow_succ]
    rcases Nat.mod_two_eq_zero_or_one k with h | h
    · rw [vP_succ_even hk h]; exact GP_symm (v_dyck k hk) ih
    · rw [vP_succ_odd hk h]; exact FP_symm (v_dyck k hk) ih

/-! ### One block to the next (proof of Proposition 4.1) -/

section
variable {L : ℕ} {V : ℕ → ℕ} (hD : Dyck L V) (hL : 2 ≤ L)
include hD hL

/-- The Conway case: if `c (L + t) = L/2 + V t` on block `L`, then `c (2L + t) = L + 𝓕(V) t`. -/
theorem c_block_succ (hB : ∀ t, t ≤ L → c (L + t) = L / 2 + V t) :
    ∀ t, t ≤ 2 * L → c (2 * L + t) = L + FP L V t := by
  have hE := hD.total
  intro t
  induction t with
  | zero =>
    intro _
    have := hB L le_rfl
    rw [show 2 * L + 0 = L + L by omega, this]; simp [FP, Arec]; omega
  | succ j ih =>
    intro hj
    have hA := FP_spec hD (show j ≤ 2 * L by omega)
    have h2 := ASpec.half hD hA
    have hs := FP_succ hD hj
    have ihj := ih (by omega)
    generalize FP L V j = r at *
    obtain ⟨_, h2', h3, _, _, _⟩ := hA
    have hstep := c_step (n := 2 * L + (j + 1)) (x := L + r) (by omega)
      (by rw [show 2 * L + (j + 1) - 1 = 2 * L + j by omega]; exact ihj) (by omega) (by omega)
    rw [hstep, show 2 * L + (j + 1) - (L + r) = L + (j + 1 - r) by omega, hB r h3,
      hB (j + 1 - r) (by omega), hs]
    omega

/-- `s` on an odd block (`s (L + t) = L/2 + t - V t`) produces the even block `L + 𝓕(V) t`. -/
theorem s_block_succ_odd (hB : ∀ t, t ≤ L → s (L + t) = L / 2 + t - V t) :
    ∀ t, t ≤ 2 * L → s (2 * L + t) = L + FP L V t := by
  have hE := hD.total
  intro t
  induction t with
  | zero =>
    intro _
    have := hB L le_rfl
    rw [show 2 * L + 0 = L + L by omega, this]; simp [FP, Arec]; omega
  | succ j ih =>
    intro hj
    have hA := FP_spec hD (show j ≤ 2 * L by omega)
    have h2 := ASpec.half hD hA
    have hs := FP_succ hD hj
    have ihj := ih (by omega)
    generalize FP L V j = r at *
    obtain ⟨_, h2', h3, _, _, _⟩ := hA
    have hstep := s_step (n := 2 * L + (j + 1)) (x := L + r) (by omega)
      (by rw [show 2 * L + (j + 1) - 1 = 2 * L + j by omega]; exact ihj) (by omega) (by omega)
    have l1 := hD.le_self r
    have l2 := hD.le_self (j + 1 - r)
    rw [hstep, show 2 * L + (j + 1) - (L + r) = L + (j + 1 - r) by omega, hB r h3,
      hB (j + 1 - r) (by omega), hs]
    omega

/-- `s` on an even block (`s (L + t) = L/2 + V t`) produces the odd block `L + t - 𝓖(V) t`.
    The boundary case `B(j) = L` reads `s` at the earlier point `2L + 1` of the new block. -/
theorem s_block_succ_even (hB : ∀ t, t ≤ L → s (L + t) = L / 2 + V t) :
    ∀ t, t ≤ 2 * L → s (2 * L + t) = L + t - GP L V t := by
  have hE := hD.total
  have hV1 : V 1 = 1 := by have := hD.half 1 (by omega); have := hD.le_self 1; omega
  have hG1 : GP L V 1 = 1 := by
    rw [GP_succ hD (j := 0) (by omega)]; simp [GP, Brec, hD.zero, hV1]
  intro t
  induction t using Nat.strong_induction_on with
  | _ t ih =>
  intro ht
  rcases t with _ | j
  · have := hB L le_rfl
    rw [show 2 * L + 0 = L + L by omega, this]; simp [GP, Brec]; omega
  · have hBs := GP_spec hD (show j ≤ 2 * L by omega)
    have hs := GP_succ hD ht
    have ihj := ih j (by omega) (by omega)
    have ih1 := ih 1
    generalize hb : GP L V j = b at *
    obtain ⟨_, h2, h3, h4, h5, _⟩ := hBs
    -- the second argument `n - s (n-1) = L + b + 1`
    have hsec : s (L + (b + 1)) = L / 2 + V (b + 1) := by
      rcases Nat.lt_or_ge b L with hbL | hbL
      · exact hB (b + 1) (by omega)
      · have hbe : b = L := by omega
        subst hbe
        have := ih1 (by omega) (by omega)
        rw [hG1] at this
        rw [show b + (b + 1) = 2 * b + 1 by omega, this, hD.tail (b + 1) (by omega)]
        omega
    have hstep := s_step (n := 2 * L + (j + 1)) (x := L + (j - b)) (by omega)
      (by rw [show 2 * L + (j + 1) - 1 = 2 * L + j by omega, ihj]; omega) (by omega) (by omega)
    rw [hstep, show 2 * L + (j + 1) - (L + (j - b)) = L + (b + 1) by omega, hsec,
      hB (j - b) (by omega), hs]
    have := hD.le_top (b + 1)
    have := hD.le_top (j - b)
    omega

end

/-! ### Proposition 4.1 -/

/-- Formula (4.1) for `s` on block `k`. -/
def sForm (k : ℕ) (Q : ℕ → ℕ) (t : ℕ) : ℕ :=
  if k % 2 = 0 then 2 ^ k / 2 + Q t else 2 ^ k / 2 + t - Q t

/-- Formula (4.1) holds on block `k`. -/
def BlockEq (k : ℕ) : Prop :=
  ∀ t, t ≤ 2 ^ k → c (2 ^ k + t) = 2 ^ k / 2 + wP k t ∧ s (2 ^ k + t) = sForm k (vP k) t

theorem block_one : BlockEq 1 := by
  intro t ht
  simp only [sForm, show (1 : ℕ) % 2 = 1 by rfl, if_neg one_ne_zero]
  show c (2 + t) = 1 + P10 t ∧ s (2 + t) = 1 + t - P10 t
  interval_cases t <;> simp [P10, c_two, c_three, c_four, s_two, s_three, s_four]

theorem block_succ {k : ℕ} (hk : 1 ≤ k) (hB : BlockEq k) : BlockEq (k + 1) := by
  have hDw := (w_props k hk).1
  have hDv := v_dyck k hk
  have hL : 2 ≤ 2 ^ k := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  have hc := c_block_succ hDw hL (fun t ht => (hB t ht).1)
  intro t ht
  rw [two_pow_succ] at ht ⊢
  rw [wP_succ hk, show 2 * 2 ^ k / 2 = 2 ^ k by omega]
  refine ⟨hc t ht, ?_⟩
  simp only [sForm, two_pow_succ, show 2 * 2 ^ k / 2 = 2 ^ k by omega]
  rcases Nat.mod_two_eq_zero_or_one k with h | h
  · rw [if_neg (by omega), vP_succ_even hk h]
    refine s_block_succ_even hDv hL (fun t ht => ?_) t ht
    have := (hB t ht).2; simp only [sForm, if_pos h] at this; exact this
  · rw [if_pos (by omega), vP_succ_odd hk h]
    refine s_block_succ_odd hDv hL (fun t ht => ?_) t ht
    have := (hB t ht).2; simp only [sForm, if_neg (by omega : ¬ k % 2 = 0)] at this; exact this

/-- Proposition 4.1: formula (4.1) holds on every block `k ≥ 1`. -/
theorem blocks : ∀ k, 1 ≤ k → BlockEq k := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => exact block_one
  | succ k hk ih => exact block_succ hk ih

end HofConway
