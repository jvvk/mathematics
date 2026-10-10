import LeanProofs.InversePairs.Sums

/-!
# Inverse pairs: the main inequality

`S p = ∑_{a=1}^{p-1} 1/√(a ā)` and `C p = (∑_{a=1}^{p-1} 1/√a)²/p`, the same sum over all pairs
`(a, b)` divided by `p`. `R p m` counts `a ∈ [2, p)` with `a ā ≤ m`.
* `R_le`: `R m ≤ (m/p) D (1 + m)^ε` from the divisor bound (Lemma 3), since `a ā = 1 + kp`;
* `Tc_le`: `Tc m ≤ m (1 + log p)`;
* `key_identity`: `S - C - 1 = ∑_m (w m - w (m+1)) (R m - Tc m / p) - w(N+1)/p`, `N = (p-1)²`;
* `main_ineq`: splitting at `Y`,
  `|S - C - 1| ≤ (L E₁ + h + 1) w(Y) + (√Y/p)(D (1+Y)^ε + 1 + log p) + 1/p`.
-/

open Finset Real

namespace InversePairs

variable (p : ℕ) [hp : Fact p.Prime]

/-- `S p = ∑_{a=1}^{p-1} 1/√(a ā)`. -/
noncomputable def S : ℝ := ∑ a ∈ Ico 1 p, w (a * inv p a)

/-- `C p = (1/p) ∑_{a,b=1}^{p-1} 1/√(ab) = (∑_{a=1}^{p-1} 1/√a)²/p`. -/
noncomputable def C : ℝ := (∑ a ∈ Ico 1 p, w a) ^ 2 / p

/-- `R p m`: the number of `a ∈ [2, p)` with `a ā ≤ m`. -/
noncomputable def R (m : ℕ) : ℕ := #{a ∈ Ico 2 p | a * inv p a ≤ m}

lemma inv_one : inv p 1 = 1 := by
  have : NeZero p := ⟨hp.out.ne_zero⟩
  have : Fact (1 < p) := ⟨hp.out.one_lt⟩
  simp [inv, ZMod.val_one]

lemma prod_mem (a : ℕ) (ha : a ∈ Ico 1 p) : 1 ≤ a * inv p a ∧ a * inv p a ≤ (p - 1) ^ 2 := by
  simp only [mem_Ico] at ha
  have hi := inv_mem p a ha.1 ha.2
  constructor
  · exact Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
  · rw [sq]; exact Nat.mul_le_mul (by omega) (by omega)

lemma Rc_eq (m : ℕ) (hm : 1 ≤ m) : Rc p m = R p m + 1 := by
  have hp2 := hp.out.two_le
  rw [Rc, R, show Ico 1 p = insert 1 (Ico 2 p) by ext a; simp; omega, filter_insert,
    ite_eq_left (by rw [inv_one]; omega), card_insert_of_notMem (by simp)]

lemma mul_inv_mod (a : ℕ) (h1 : 1 ≤ a) (h2 : a < p) : a * inv p a % p = 1 := by
  have hp1 := hp.out.one_lt
  have hcast : ((a * inv p a : ℕ) : ZMod p) = ((1 : ℕ) : ZMod p) := by
    push_cast
    rw [inv, ZMod.natCast_zmod_val, mul_inv_cancel₀ (cast_ne_zero p a h1 h2)]
  rw [ZMod.natCast_eq_natCast_iff'] at hcast
  rw [hcast, Nat.mod_eq_of_lt hp1]

/-- Lemma 3, first half: every `a` counted by `R m` divides some `1 + kp` with `1 ≤ k ≤ m/p`. -/
lemma R_le_div (m : ℕ) :
    R p m ≤ ∑ k ∈ Icc 1 (m / p), #(1 + k * p).divisors := by
  refine (card_le_card fun a ha => ?_).trans card_biUnion_le
  simp only [mem_filter, mem_Ico] at ha
  obtain ⟨⟨h2, hap⟩, hm⟩ := ha
  have hi := inv_mem p a (by omega) hap
  have hmod := mul_inv_mod p a (by omega) hap
  have hdiv := Nat.div_add_mod (a * inv p a) p
  rw [hmod] at hdiv
  generalize a * inv p a / p = k at hdiv
  have hprod : 2 ≤ a * inv p a := by have := Nat.mul_le_mul h2 hi.1; omega
  have hk1 : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · subst h0; omega
    · exact h0
  have hkm : k ≤ m / p := (Nat.le_div_iff_mul_le hp.out.pos).2 (by rw [Nat.mul_comm]; omega)
  simp only [mem_biUnion, mem_Icc, Nat.mem_divisors]
  refine ⟨k, ⟨hk1, hkm⟩, ⟨⟨inv p a, by rw [Nat.mul_comm k p]; omega⟩, by omega⟩⟩

/-- Lemma 3: `R m ≤ (m/p) D (1 + m)^ε`. -/
lemma R_le (m : ℕ) (D ε : ℝ) (hε : 0 ≤ ε) (hD0 : 0 ≤ D)
    (hD : ∀ n : ℕ, n ≠ 0 → (#n.divisors : ℝ) ≤ D * (n : ℝ) ^ ε) :
    (R p m : ℝ) ≤ (m : ℝ) / p * (D * (1 + m) ^ ε) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  calc (R p m : ℝ) ≤ ∑ k ∈ Icc 1 (m / p), (#(1 + k * p).divisors : ℝ) := by
        exact_mod_cast R_le_div p m
    _ ≤ ∑ k ∈ Icc 1 (m / p), D * (1 + m : ℝ) ^ ε := by
        refine sum_le_sum fun k hk => (hD _ (by omega)).trans ?_
        simp only [mem_Icc] at hk
        have : ((1 + k * p : ℕ) : ℝ) ≤ 1 + m := by
          have : k * p ≤ m := (Nat.le_div_iff_mul_le hp.out.pos).1 hk.2
          exact_mod_cast (by omega : 1 + k * p ≤ 1 + m)
        gcongr
    _ = (m / p : ℕ) * (D * (1 + m : ℝ) ^ ε) := by simp
    _ ≤ (m : ℝ) / p * (D * (1 + m) ^ ε) := by
        gcongr
        exact Nat.cast_div_le

lemma Tc_le (m : ℕ) : (Tc p m : ℝ) ≤ m * (1 + Real.log p) := by
  calc (Tc p m : ℝ) ≤ ∑ a ∈ Ico 1 p, (m : ℝ) * (1 / (a : ℝ)) := by
        rw [Tc, Nat.cast_sum]
        refine sum_le_sum fun a ha => ?_
        simp only [mem_Ico] at ha
        calc ((min (p - 1) (m / a) : ℕ) : ℝ) ≤ ((m / a : ℕ) : ℝ) := by
              exact_mod_cast min_le_right _ _
          _ ≤ (m : ℝ) / a := Nat.cast_div_le
          _ = m * (1 / a) := by ring
    _ = m * ∑ a ∈ Ico 1 p, (1 / (a : ℝ)) := by rw [mul_sum]
    _ ≤ m * (1 + Real.log p) := by gcongr; exact sum_inv_le p

lemma w_one : w 1 = 1 := by simp [w]

lemma w_le_one (m : ℕ) (hm : 1 ≤ m) : w m ≤ 1 := by
  simp only [w]
  rw [div_le_one (Real.sqrt_pos.2 (by exact_mod_cast hm))]
  rw [show (1 : ℝ) = Real.sqrt 1 by simp]
  exact Real.sqrt_le_sqrt (by exact_mod_cast hm)

lemma w_nonneg (m : ℕ) : 0 ≤ w m := by simp only [w]; positivity

/-- `S - C - 1 = ∑_m (w m - w(m+1)) (R m - Tc m/p) - w(N+1)/p` with `N = (p-1)²`. -/
lemma key_identity :
    S p - C p - 1 = ∑ m ∈ Icc 1 ((p - 1) ^ 2), (w m - w (m + 1)) * ((R p m : ℝ) - Tc p m / p)
      - w ((p - 1) ^ 2 + 1) / p := by
  have hp2 := hp.out.two_le
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  set N := (p - 1) ^ 2
  have hS := layer (Ico 1 p) (fun a => a * inv p a) N (prod_mem p) w
  have hP := layer (Ico 1 p ×ˢ Ico 1 p) (fun x => x.1 * x.2) N (fun x hx => by
    simp only [mem_product, mem_Ico] at hx
    refine ⟨Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega)), ?_⟩
    exact (Nat.mul_le_mul (by omega) (by omega)).trans_eq (sq (p - 1)).symm) w
  simp only [← Tc_eq, card_product, Nat.card_Ico] at hP
  rw [grid_sum] at hP
  have hRc : ∀ m ∈ Icc 1 N, (#{a ∈ Ico 1 p | a * inv p a ≤ m} : ℝ) = R p m + 1 := fun m hm => by
    have := Rc_eq p m (mem_Icc.1 hm).1; rw [Rc] at this; exact_mod_cast this
  have htel : ∑ m ∈ Icc 1 N, (w m - w (m + 1)) = 1 - w (N + 1) := by
    rw [show Icc 1 N = Ico 1 (N + 1) by ext; simp only [mem_Icc, mem_Ico]; omega,
      telescope w 1 (N + 1) (by omega), w_one]
  rw [S, C, hS, sum_congr rfl fun m hm => by rw [hRc m hm], Nat.card_Ico]
  rw [show (∑ a ∈ Ico 1 p, w a) ^ 2 / (p : ℝ) =
    (∑ m ∈ Icc 1 N, (w m - w (m + 1)) * (Tc p m : ℝ) + w (N + 1) * ((p - 1) * (p - 1) : ℕ)) / p
    by rw [hP]]
  have e1 : ∑ m ∈ Icc 1 N, (w m - w (m + 1)) * ((R p m : ℝ) + 1) =
      ∑ m ∈ Icc 1 N, (w m - w (m + 1)) * (R p m : ℝ) + (1 - w (N + 1)) := by
    rw [← htel, ← sum_add_distrib]; exact sum_congr rfl fun m _ => by ring
  have e2 : ∑ m ∈ Icc 1 N, (w m - w (m + 1)) * ((R p m : ℝ) - Tc p m / p) =
      ∑ m ∈ Icc 1 N, (w m - w (m + 1)) * (R p m : ℝ) -
        (∑ m ∈ Icc 1 N, (w m - w (m + 1)) * (Tc p m : ℝ)) / p := by
    rw [sum_div, ← sum_sub_distrib]; exact sum_congr rfl fun m _ => by ring
  rw [e1, e2]
  push_cast [Nat.cast_sub hp.out.one_le]
  field_simp
  ring

/-- The main inequality. -/
theorem main_ineq (hW : WeilBound p) (h L Y : ℕ) (hh : 1 ≤ h) (hL : p ≤ 1 + L * h) (hY : 1 ≤ Y)
    (D ε : ℝ) (hε : 0 ≤ ε) (hD0 : 0 ≤ D)
    (hD : ∀ n : ℕ, n ≠ 0 → (#n.divisors : ℝ) ≤ D * (n : ℝ) ^ ε) :
    |S p - C p - 1| ≤ (L * E1 p + h + 1) * w Y +
      Real.sqrt Y / p * (D * (1 + Y) ^ ε + 1 + Real.log p) + 1 / p := by
  have hp2 := hp.out.two_le
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  have hlog : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hp.out.one_le)
  set N := (p - 1) ^ 2
  set B := D * (1 + Y) ^ ε + 1 + Real.log p
  have hdw : ∀ m ∈ Icc 1 N, 0 ≤ w m - w (m + 1) := fun m hm => dw_nonneg m (mem_Icc.1 hm).1
  rw [key_identity]
  -- the sum, split at `Y`
  set F := fun m : ℕ => (w m - w (m + 1)) * ((R p m : ℝ) - Tc p m / p)
  have hsplit := sum_filter_add_sum_filter_not (Icc 1 N) (fun m => m < Y) F
  -- small products
  have hsmall : |∑ m ∈ (Icc 1 N).filter (· < Y), F m| ≤ Real.sqrt Y / p * B := by
    refine (abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ m ∈ (Icc 1 N).filter (· < Y), |F m|
        ≤ ∑ m ∈ (Icc 1 N).filter (· < Y), (w m - w (m + 1)) * ((m : ℝ) / p * B) := by
          refine sum_le_sum fun m hm => ?_
          simp only [mem_filter, mem_Icc] at hm
          have hd := hdw m (mem_Icc.2 hm.1)
          simp only [F]
          rw [abs_mul, abs_of_nonneg hd]
          refine mul_le_mul_of_nonneg_left ?_ hd
          have hR := R_le p m D ε hε hD0 hD
          have hT := Tc_le p m
          have hR0 : (0 : ℝ) ≤ R p m := by positivity
          have hT0 : (0 : ℝ) ≤ Tc p m / p := by positivity
          have hmY : (1 + m : ℝ) ^ ε ≤ (1 + Y) ^ ε := by
            gcongr; exact_mod_cast hm.2.le
          have hm0 : (0 : ℝ) ≤ m / p := by positivity
          calc |(R p m : ℝ) - Tc p m / p| ≤ R p m + Tc p m / p := by
                rw [abs_le]; constructor <;> linarith
            _ ≤ (m : ℝ) / p * (D * (1 + Y) ^ ε) + m * (1 + Real.log p) / p := by
                have : (Tc p m : ℝ) / p ≤ m * (1 + Real.log p) / p :=
                  div_le_div_of_nonneg_right hT hp0.le
                have : (m : ℝ) / p * (D * (1 + m) ^ ε) ≤ (m : ℝ) / p * (D * (1 + Y) ^ ε) := by
                  gcongr
                linarith
            _ = (m : ℝ) / p * B := by simp only [B]; ring
      _ ≤ ∑ m ∈ Ico 1 Y, (w m - w (m + 1)) * ((m : ℝ) / p * B) := by
          refine sum_le_sum_of_subset_of_nonneg (fun m hm => ?_) (fun m hm _ => ?_)
          · simp only [mem_filter, mem_Icc] at hm; simp only [mem_Ico]; omega
          · simp only [mem_Ico] at hm
            have := dw_nonneg m hm.1
            have : (0 : ℝ) ≤ B := by positivity
            positivity
      _ = B / p * ∑ m ∈ Ico 1 Y, (m : ℝ) * (w m - w (m + 1)) := by
          rw [mul_sum]; exact sum_congr rfl fun m _ => by ring
      _ ≤ B / p * ∑ m ∈ Ico 1 Y, w m / 2 := by
          gcongr with m hm
          exact m_dw_le m (mem_Ico.1 hm).1
      _ ≤ B / p * Real.sqrt Y := by
          gcongr
          rw [← sum_div]; linarith [sum_w_le Y]
      _ = Real.sqrt Y / p * B := by ring
  -- large products
  have hlarge : |∑ m ∈ (Icc 1 N).filter (fun m => ¬ m < Y), F m| ≤ (L * E1 p + h + 1) * w Y := by
    refine (abs_sum_le_sum_abs _ _).trans ?_
    have hE : 0 ≤ (L * E1 p + h + 1 : ℝ) := by
      have : 0 ≤ E1 p := by rw [E1]; positivity
      positivity
    calc ∑ m ∈ (Icc 1 N).filter (fun m => ¬ m < Y), |F m|
        ≤ ∑ m ∈ (Icc 1 N).filter (fun m => ¬ m < Y), (w m - w (m + 1)) * (L * E1 p + h + 1) := by
          refine sum_le_sum fun m hm => ?_
          simp only [mem_filter, mem_Icc] at hm
          have hd := hdw m (mem_Icc.2 hm.1)
          simp only [F]
          rw [abs_mul, abs_of_nonneg hd]
          refine mul_le_mul_of_nonneg_left ?_ hd
          have hs := stair p hW m h L hh hL
          have hRc : (Rc p m : ℝ) = R p m + 1 := by exact_mod_cast Rc_eq p m hm.1.1
          rw [hRc] at hs
          rw [abs_le] at hs ⊢; constructor <;> linarith [hs.1, hs.2]
      _ = (∑ m ∈ (Icc 1 N).filter (fun m => ¬ m < Y), (w m - w (m + 1))) * (L * E1 p + h + 1) := by
          rw [sum_mul]
      _ ≤ w Y * (L * E1 p + h + 1) := by
          gcongr
          rcases Nat.lt_or_ge (N + 1) Y with hNY | hNY
          · rw [filter_false_of_mem fun m hm => by simp only [mem_Icc] at hm; omega]
            simp only [sum_empty]; exact w_nonneg Y
          · calc ∑ m ∈ (Icc 1 N).filter (fun m => ¬ m < Y), (w m - w (m + 1))
                ≤ ∑ m ∈ Ico Y (N + 1), (w m - w (m + 1)) := by
                  refine sum_le_sum_of_subset_of_nonneg (fun m hm => ?_) (fun m hm _ => ?_)
                  · simp only [mem_filter, mem_Icc] at hm; simp only [mem_Ico]; omega
                  · simp only [mem_Ico] at hm; exact dw_nonneg m (by omega)
              _ = w Y - w (N + 1) := telescope w Y (N + 1) hNY
              _ ≤ w Y := by linarith [w_nonneg (N + 1)]
      _ = (L * E1 p + h + 1) * w Y := by ring
  have hlast : |w (N + 1) / p| ≤ 1 / p := by
    rw [abs_of_nonneg (by have := w_nonneg (N + 1); positivity)]
    exact div_le_div_of_nonneg_right (w_le_one _ (by omega)) hp0.le
  calc |∑ m ∈ Icc 1 N, (w m - w (m + 1)) * ((R p m : ℝ) - Tc p m / p) - w (N + 1) / p|
      ≤ |∑ m ∈ Icc 1 N, F m| + |w (N + 1) / p| := abs_sub _ _
    _ ≤ (|∑ m ∈ (Icc 1 N).filter (· < Y), F m| +
          |∑ m ∈ (Icc 1 N).filter (fun m => ¬ m < Y), F m|) + 1 / p := by
        rw [← hsplit]; gcongr; exact abs_add_le _ _
    _ ≤ _ := by linarith

end InversePairs
