import LeanProofs.Frobenius292507.Carry

/-!
# MO 292507: step 6, digit vectors and the mixed radix

A digit vector is `d` with `0 ≤ dᵢ < a_{i-1}` (`b₀ = aₙ₋₁`). Its value is `v d = ∑ dᵢ πᵢ`.
The place values `π₀ = 1, πₙ₋₁, …, π₁` with radices `aₙ₋₁, aₙ₋₂, …, a₀` form a mixed radix.
We run it through the suffix sums `F lo = ∑_{lo ≤ i ≤ n} eᵢ ∏_{i ≤ j < n} aⱼ` with `eᵢ < aᵢ₋₁`
(the digit `d₀` sits at `i = n`):

* `F_bound`: `F lo + 1 ≤ ∏_{lo-1 ≤ j < n} aⱼ`, with equality iff every digit is maximal.
* `F_surj`: every `t < ∏_{lo-1 ≤ j < n} aⱼ` is some `F lo` (division algorithm).
* `v_le`, `v_eq_N`, `v_surj`: (ii) `v d ≤ N` with equality only for the maximal vector, and
  (i) every `t ≤ N` is `v d` for a digit vector `d`.
-/

namespace Frobenius292507

open Finset

variable {n : ℕ} {a : ℕ → ℕ}

/-- `d` is a digit vector: `dᵢ < bᵢ = a_{i-1}` for `i < n`. -/
def IsDigit (n : ℕ) (a : ℕ → ℕ) (d : ℕ → ℕ) : Prop := ∀ i < n, d i < b n a i

/-- The mixed-radix value `v d = ∑ dᵢ πᵢ`. -/
def v (n : ℕ) (a : ℕ → ℕ) (d : ℕ → ℕ) : ℕ := ∑ i ∈ range n, d i * pi n a i

/-- Suffix sums of the mixed radix. -/
def F (n : ℕ) (a e : ℕ → ℕ) (lo : ℕ) : ℕ := ∑ i ∈ Ico lo (n + 1), e i * ∏ j ∈ Ico i n, a j

lemma F_bound (hpos : ∀ i, 0 < a i) (e : ℕ → ℕ) : ∀ k lo, lo + k = n + 1 → 1 ≤ lo →
    (∀ i ∈ Ico lo (n + 1), e i < a (i - 1)) →
    F n a e lo + 1 ≤ ∏ j ∈ Ico (lo - 1) n, a j ∧
    (F n a e lo + 1 = ∏ j ∈ Ico (lo - 1) n, a j → ∀ i ∈ Ico lo (n + 1), e i + 1 = a (i - 1)) := by
  intro k
  induction k with
  | zero =>
    intro lo hlo _ _
    obtain rfl : lo = n + 1 := by omega
    simp [F]
  | succ k ih =>
    intro lo hlo h1 hd
    obtain ⟨ihle, iheq⟩ := ih (lo + 1) (by omega) (by omega)
      fun i hi => hd i (by simp only [mem_Ico] at hi ⊢; omega)
    rw [Nat.add_sub_cancel] at ihle iheq
    have hF : F n a e lo = e lo * ∏ j ∈ Ico lo n, a j + F n a e (lo + 1) := by
      unfold F; rw [sum_eq_sum_Ico_succ_bot (by omega)]
    have hQ : ∏ j ∈ Ico (lo - 1) n, a j = a (lo - 1) * ∏ j ∈ Ico lo n, a j := by
      rw [prod_eq_prod_Ico_succ_bot (by omega), Nat.sub_add_cancel h1]
    have hpos' : 0 < ∏ j ∈ Ico lo n, a j := prod_pos fun i _ => hpos i
    have hE : e lo + 1 ≤ a (lo - 1) := hd lo (by simp only [mem_Ico]; omega)
    have hmul : e lo * ∏ j ∈ Ico lo n, a j + ∏ j ∈ Ico lo n, a j
        ≤ a (lo - 1) * ∏ j ∈ Ico lo n, a j := by
      have := Nat.mul_le_mul_right (∏ j ∈ Ico lo n, a j) hE
      rwa [add_mul, one_mul] at this
    rw [hF, hQ]
    refine ⟨by omega, fun heq => ?_⟩
    have hG : F n a e (lo + 1) + 1 = ∏ j ∈ Ico lo n, a j := by omega
    have hA : (e lo + 1) * ∏ j ∈ Ico lo n, a j = a (lo - 1) * ∏ j ∈ Ico lo n, a j := by
      rw [add_mul, one_mul]; omega
    have hA' := Nat.eq_of_mul_eq_mul_right hpos' hA
    intro i hi
    rcases Nat.eq_or_lt_of_le (mem_Ico.1 hi).1 with h | h
    · subst h; exact hA'
    · exact iheq hG i (by simp only [mem_Ico] at hi ⊢; omega)

lemma F_surj (hpos : ∀ i, 0 < a i) : ∀ k lo, lo + k = n + 1 → 1 ≤ lo →
    ∀ t < ∏ j ∈ Ico (lo - 1) n, a j,
      ∃ e : ℕ → ℕ, (∀ i ∈ Ico lo (n + 1), e i < a (i - 1)) ∧ F n a e lo = t := by
  intro k
  induction k with
  | zero =>
    intro lo hlo _ t ht
    obtain rfl : lo = n + 1 := by omega
    refine ⟨0, by simp, ?_⟩
    simp only [Nat.add_sub_cancel, Ico_self, prod_empty] at ht
    simp [F]; omega
  | succ k ih =>
    intro lo hlo h1 t ht
    set Q := ∏ j ∈ Ico lo n, a j with hQdef
    have hpos' : 0 < Q := prod_pos fun i _ => hpos i
    have hQ : ∏ j ∈ Ico (lo - 1) n, a j = a (lo - 1) * Q := by
      rw [prod_eq_prod_Ico_succ_bot (by omega), Nat.sub_add_cancel h1]
    obtain ⟨e, he, hFe⟩ := ih (lo + 1) (by omega) (by omega) (t % Q)
      (by rw [Nat.add_sub_cancel]; exact Nat.mod_lt _ hpos')
    refine ⟨fun i => if i = lo then t / Q else e i, fun i hi => ?_, ?_⟩
    · by_cases h : i = lo
      · subst h
        simp only [ite_true]
        rw [Nat.div_lt_iff_lt_mul hpos']
        rw [hQ] at ht; exact ht
      · simp only [h, ite_false]
        exact he i (by simp only [mem_Ico] at hi ⊢; omega)
    · have hF : ∀ f : ℕ → ℕ, F n a f lo = f lo * Q + F n a f (lo + 1) := fun f => by
        unfold F; rw [sum_eq_sum_Ico_succ_bot (by omega)]
      rw [hF]
      have : F n a (fun i => if i = lo then t / Q else e i) (lo + 1) = F n a e (lo + 1) := by
        unfold F
        refine sum_congr rfl fun i hi => ?_
        have : i ≠ lo := by simp only [mem_Ico] at hi; omega
        simp only [this, ite_false]
      rw [this, hFe]
      simp only [ite_true]
      exact Nat.div_add_mod' t Q

/-- Every `j < n` is `i % n` for some `1 ≤ i ≤ n` (namely `i = j`, or `i = n` when `j = 0`). -/
lemma exists_Ico_mod {j : ℕ} (hj : j < n) : ∃ i ∈ Ico 1 (n + 1), i % n = j := by
  by_cases h : j = 0
  · exact ⟨n, by simp only [mem_Ico]; omega, by simp [h]⟩
  · exact ⟨j, by simp only [mem_Ico]; omega, Nat.mod_eq_of_lt hj⟩

lemma b_mod (hper : ∀ i, a (i + n) = a i) {i : ℕ} (hi : i ∈ Ico 1 (n + 1)) :
    b n a (i % n) = a (i - 1) := by
  rw [mem_Ico] at hi
  rcases Nat.lt_or_ge i n with h | h
  · rw [Nat.mod_eq_of_lt h, b, show i + n - 1 = (i - 1) + n by omega, hper]
  · obtain rfl : i = n := by omega
    rw [Nat.mod_self, b, Nat.zero_add]

lemma pi_mod {i : ℕ} (hi : i ∈ Ico 1 (n + 1)) : pi n a (i % n) = ∏ j ∈ Ico i n, a j := by
  rw [mem_Ico] at hi
  rcases Nat.lt_or_ge i n with h | h
  · rw [Nat.mod_eq_of_lt h, pi, ite_eq_right (by omega)]
  · obtain rfl : i = n := by omega
    simp [pi]

lemma v_eq_F (d : ℕ → ℕ) :
    v n a d = F n a (fun i => d (i % n)) 1 := by
  unfold v F
  rw [sum_Ico_eq_sum_range, Nat.add_sub_cancel]
  set g : ℕ → ℕ := fun i => d (i % n) * pi n a (i % n) with hg
  symm
  calc ∑ k ∈ range n, d ((1 + k) % n) * ∏ j ∈ Ico (1 + k) n, a j
      = ∑ k ∈ range n, g (k + 1) := sum_congr rfl fun k hk => by
        change _ = d ((k + 1) % n) * pi n a ((k + 1) % n)
        rw [Nat.add_comm k 1,
          pi_mod (a := a) (show 1 + k ∈ Ico 1 (n + 1) by simp only [mem_Ico]; simp at hk; omega)]
    _ = ∑ k ∈ range n, g k := sum_shift (fun i => by simp [hg]) 1
    _ = ∑ k ∈ range n, d k * pi n a k :=
        sum_congr rfl fun i hi => by
          change d (i % n) * pi n a (i % n) = _
          rw [Nat.mod_eq_of_lt (mem_range.1 hi)]

lemma digit_F (hper : ∀ i, a (i + n) = a i) {d : ℕ → ℕ} (hd : IsDigit n a d) :
    ∀ i ∈ Ico 1 (n + 1), d (i % n) < a (i - 1) := fun i hi => by
  rw [← b_mod hper hi]
  exact hd _ (Nat.mod_lt _ (by simp only [mem_Ico] at hi; omega))

lemma P_eq : ∏ j ∈ Ico (1 - 1) n, a j = P n a := by
  rw [Nat.sub_self, Nat.Ico_zero_eq_range]; rfl

/-- **Step 6 (ii)**: `v d ≤ N`. -/
lemma v_le (hper : ∀ i, a (i + n) = a i) (hpos : ∀ i, 0 < a i) {d : ℕ → ℕ}
    (hd : IsDigit n a d) : v n a d ≤ N n a := by
  have := (F_bound (n := n) hpos (fun i => d (i % n)) n 1 (by omega) le_rfl (digit_F hper hd)).1
  rw [P_eq, ← v_eq_F] at this
  unfold N; omega

/-- **Step 6 (ii)**: `v d = N` only for the maximal vector `dᵢ = a_{i-1} - 1`. -/
lemma v_eq_N (hper : ∀ i, a (i + n) = a i) (hpos : ∀ i, 0 < a i) {d : ℕ → ℕ}
    (hd : IsDigit n a d) (hv : v n a d = N n a) : ∀ i < n, d i = b n a i - 1 := by
  have := (F_bound (n := n) hpos (fun i => d (i % n)) n 1 (by omega) le_rfl (digit_F hper hd)).2
  rw [P_eq, ← v_eq_F] at this
  have hP := P_pos (n := n) hpos
  have hall := this (by unfold N at hv; omega)
  intro j hj
  obtain ⟨i, hi, rfl⟩ := exists_Ico_mod hj
  have := hall i hi
  rw [b_mod hper hi]
  beta_reduce at this
  omega

/-- **Step 6 (i)** (existence): every `t ≤ N` is `v d` for some digit vector `d`. -/
lemma v_surj (hn : 1 ≤ n) (hper : ∀ i, a (i + n) = a i) (hpos : ∀ i, 0 < a i) {t : ℕ}
    (ht : t ≤ N n a) : ∃ d, IsDigit n a d ∧ v n a d = t := by
  have hP := P_pos (n := n) hpos
  obtain ⟨e, he, hFe⟩ :=
    F_surj (n := n) hpos n 1 (by omega) le_rfl t (by rw [P_eq]; unfold N at ht; omega)
  refine ⟨fun i => e (if i = 0 then n else i), fun j hj => ?_, ?_⟩
  · obtain ⟨i, hi, rfl⟩ := exists_Ico_mod hj
    rw [b_mod hper hi]
    have hi' := mem_Ico.1 hi
    rcases Nat.lt_or_ge i n with h | h
    · simp only [Nat.mod_eq_of_lt h, ite_eq_right (show i ≠ 0 by omega)]; exact he i hi
    · obtain rfl : i = n := by omega
      simp only [Nat.mod_self, ite_true]; exact he i hi
  · rw [v_eq_F, ← hFe]
    unfold F
    refine sum_congr rfl fun i hi => ?_
    have hi' := mem_Ico.1 hi
    congr 1
    rcases Nat.lt_or_ge i n with h | h
    · simp only [Nat.mod_eq_of_lt h, ite_eq_right (show i ≠ 0 by omega)]
    · obtain rfl : i = n := by omega
      simp only [Nat.mod_self, ite_true]

lemma pi_pos (hpos : ∀ i, 0 < a i) (i : ℕ) : 0 < pi n a i := by
  unfold pi; split_ifs
  · exact Nat.one_pos
  · exact prod_pos fun j _ => hpos j

end Frobenius292507
