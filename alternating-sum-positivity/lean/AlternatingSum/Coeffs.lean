import AlternatingSum.Main

/-!
  The coefficients of `R^(m+1)`, from equation (4) of the paper,
  `R = (1-z)^-2 / (1 - w² (1-z)^-2)`:
  `[w^x z^y] R^(m+1) = C(m + x/2, m) C(2m + x + 1 + y, y)` for even `x`, and `0` for odd `x`.
-/

namespace Abdesselam

open MvPowerSeries Finset

theorem mono_zero_left (t : ℕ) : mono 0 t = Finsupp.single 1 t := by simp [mono]

/-- Coefficients of a product with a series in `z` only. -/
theorem coeff_zonly_mul (f : PowerSeries ℚ) (F : PS) (x y : ℕ) :
    coeff (mono x y) (PowerSeries.subst (X 1 : PS) f * F) =
      ∑ t ∈ range (y + 1), PowerSeries.coeff t f * coeff (mono x (y - t)) F := by
  classical
  have hval : ∀ p : (Fin 2 →₀ ℕ) × (Fin 2 →₀ ℕ), p.1 + p.2 = mono x y →
      p.1 0 + p.2 0 = x ∧ p.1 1 + p.2 1 = y := by
    intro p h
    exact ⟨by simpa using congrArg (· 0) h, by simpa using congrArg (· 1) h⟩
  rw [coeff_mul, ← sum_filter_of_ne (p := fun p ↦ p.1 0 = 0)]
  · refine sum_nbij' (fun p ↦ p.1 1) (fun t ↦ (mono 0 t, mono x (y - t))) ?_ ?_ ?_ ?_ ?_
    · intro p hp
      simp only [mem_filter, mem_antidiagonal] at hp
      simp only [mem_range]
      have := hval p hp.1; omega
    · intro t ht
      simp only [mem_range] at ht
      simp only [mem_filter, mem_antidiagonal, mono_add, mono_zero, mono_inj]
      exact ⟨⟨by omega, by omega⟩, trivial⟩
    · intro p hp
      simp only [mem_filter, mem_antidiagonal] at hp
      have h := hval p hp.1
      ext t <;> fin_cases t <;> simp <;> omega
    · intro t _; simp
    · intro p hp
      simp only [mem_filter, mem_antidiagonal] at hp
      have h := hval p hp.1
      have h1 : p.1 = Finsupp.single 1 (p.1 1) := by
        ext t; fin_cases t <;> simp [hp.2]
      have h2 : p.2 = mono x (y - p.1 1) := by
        ext t; fin_cases t <;> simp <;> omega
      rw [PowerSeries.coeff_subst_single, ite_eq_left h1, h2]
  · intro p _ hne
    by_contra h0
    apply hne
    rw [PowerSeries.coeff_subst_single, ite_eq_right, zero_mul]
    intro h; exact h0 (by rw [h]; simp)

/-- Coefficients of a product with a power of `w`. -/
theorem coeff_wpow_mul (k : ℕ) (F : PS) (x y : ℕ) :
    coeff (mono x y) (X 0 ^ k * F) = if k ≤ x then coeff (mono (x - k) y) F else 0 := by
  classical
  rw [X_pow_eq, coeff_monomial_mul]
  have hle : Finsupp.single 0 k ≤ mono x y ↔ k ≤ x := by
    constructor
    · intro h; simpa using h 0
    · intro h t; fin_cases t <;> simp [h]
  have hsub : mono x y - Finsupp.single 0 k = mono (x - k) y := by
    ext t; fin_cases t <;> simp
  by_cases h : k ≤ x
  · rw [ite_eq_left (hle.2 h), ite_eq_left h, hsub, one_mul]
  · rw [ite_eq_right (fun h' ↦ h (hle.1 h')), ite_eq_right h]

/-- `inv1 m · (1 - a)^(m+1) = 1` after any legal substitution. -/
theorem subst_inv1_mul' (m : ℕ) (a : PS) (ha : PowerSeries.HasSubst a) :
    PowerSeries.subst a (inv1 m) * (1 - a) ^ (m + 1) = 1 := by
  have h := congrArg (PowerSeries.substAlgHom ha)
    (PowerSeries.mk_add_choose_mul_one_sub_pow_eq_one (S := ℚ) (d := m))
  simp only [map_mul, map_pow, map_sub, map_one, PowerSeries.substAlgHom_X,
    PowerSeries.coe_substAlgHom] at h
  exact h

/-- `(1-z)^-2`. -/
noncomputable def B : PS := PowerSeries.subst (X 1 : PS) (inv1 1)

theorem B_mul : B * (1 - X 1) ^ 2 = 1 := subst_inv1_mul 1 1

theorem hasSubst_wB : PowerSeries.HasSubst (X 0 ^ 2 * B : PS) :=
  PowerSeries.HasSubst.of_constantCoeff_zero (by simp)

/-- `(1 - w² (1-z)^-2)^-(m+1)`. -/
noncomputable def Q (m : ℕ) : PS := PowerSeries.subst (X 0 ^ 2 * B) (inv1 m)

theorem Bpow (k : ℕ) : B ^ k = PowerSeries.subst (X 1 : PS) (inv1 1 ^ k) := by
  rw [B, PowerSeries.subst_pow (PowerSeries.HasSubst.X 1)]

/-- Equation (4): `R^(m+1) = (1-z)^-(2m+2) (1 - w²(1-z)^-2)^-(m+1)`. -/
theorem R_pow (m : ℕ) : R ^ (m + 1) = B ^ (m + 1) * Q m := by
  have hE : E = (1 - X 0 ^ 2 * B) * (1 - X 1) ^ 2 := by
    rw [E, sub_mul, one_mul, mul_assoc, B_mul, mul_one]
  have h1 : B ^ (m + 1) * Q m * E ^ (m + 1) = 1 := by
    have hQ := subst_inv1_mul' m _ hasSubst_wB
    rw [← Q] at hQ
    have hB := B_mul
    rw [hE]
    generalize (1 - X 1 : PS) ^ 2 = T at hB ⊢
    generalize (1 - X 0 ^ 2 * B : PS) = U at hQ ⊢
    calc _ = (B * T) ^ (m + 1) * (Q m * U ^ (m + 1)) := by ring
      _ = 1 := by rw [hB, hQ, one_pow, one_mul]
  calc R ^ (m + 1) = R ^ (m + 1) * (B ^ (m + 1) * Q m * E ^ (m + 1)) := by rw [h1, mul_one]
    _ = B ^ (m + 1) * Q m * (R * E) ^ (m + 1) := by ring
    _ = B ^ (m + 1) * Q m := by rw [R_mul_E, one_pow, mul_one]

theorem coeff_inv1 (m t : ℕ) : PowerSeries.coeff t (inv1 m) = ((m + t).choose m : ℚ) := by
  simp [inv1]

/-- `((1-t)^-2)^(j+1) = (1-t)^-(2j+2)`. -/
theorem inv1_one_pow (j : ℕ) : inv1 1 ^ (j + 1) = inv1 (2 * j + 1) := by
  have hne : ((1 : PowerSeries ℚ) - PowerSeries.X) ^ (2 * j + 2) ≠ 0 := by
    refine pow_ne_zero _ fun h ↦ ?_
    have := congrArg PowerSeries.constantCoeff h
    simp at this
  have h1 : inv1 1 ^ (j + 1) * (1 - PowerSeries.X) ^ (2 * j + 2) = 1 := by
    have h := PowerSeries.mk_add_choose_mul_one_sub_pow_eq_one (S := ℚ) (d := 1)
    rw [show 2 * j + 2 = 2 * (j + 1) by ring, pow_mul, ← mul_pow]
    change (inv1 1 * (1 - PowerSeries.X) ^ (1 + 1)) ^ (j + 1) = 1 at *
    rw [show inv1 1 * (1 - PowerSeries.X) ^ (1 + 1) = 1 from h, one_pow]
  have h2 : inv1 (2 * j + 1) * (1 - PowerSeries.X) ^ (2 * j + 2) = 1 :=
    PowerSeries.mk_add_choose_mul_one_sub_pow_eq_one (S := ℚ) (d := 2 * j + 1)
  exact mul_right_cancel₀ hne (h1.trans h2.symm)

theorem coeff_Bpow (k x y : ℕ) :
    coeff (mono x y) (B ^ k) = if x = 0 then PowerSeries.coeff y (inv1 1 ^ k) else 0 := by
  classical
  rw [Bpow, PowerSeries.coeff_subst_single]
  simp only [mono_one]
  congr 1
  apply propext
  constructor
  · intro h; simpa using congrArg (· 0) h
  · rintro rfl; exact mono_zero_left y

theorem coeff_Q (m x y : ℕ) :
    coeff (mono x y) (Q m) =
      if Even x then ((m + x / 2).choose m : ℚ) * PowerSeries.coeff y (inv1 1 ^ (x / 2)) else 0 := by
  classical
  rw [Q, PowerSeries.coeff_subst hasSubst_wB]
  have hterm : ∀ h : ℕ, PowerSeries.coeff h (inv1 m) • coeff (mono x y) ((X 0 ^ 2 * B) ^ h) =
      if x = 2 * h then ((m + h).choose m : ℚ) * PowerSeries.coeff y (inv1 1 ^ h) else 0 := by
    intro h
    rw [mul_pow, ← pow_mul, coeff_wpow_mul, coeff_Bpow, coeff_inv1, smul_eq_mul]
    by_cases hx : x = 2 * h
    · rw [ite_eq_left (by omega), ite_eq_left (by omega), ite_eq_left hx]
    · rw [ite_eq_right hx]
      split_ifs <;> first | omega | simp
  simp_rw [hterm]
  split_ifs with hx
  · obtain ⟨r, hr⟩ := hx
    rw [finsum_eq_single _ (x / 2)]
    · rw [ite_eq_left (by omega)]
    · intro h hh; rw [ite_eq_right (by omega)]
  · rw [finsum_eq_zero_of_forall_eq_zero]
    intro h; rw [ite_eq_right]; rintro rfl; exact hx ⟨h, by ring⟩

/-- **Coefficients of `R^(m+1)`** (equation (4) expanded). -/
theorem coeff_R_pow (m x y : ℕ) :
    coeff (mono x y) (R ^ (m + 1)) =
      if Even x then ((m + x / 2).choose m : ℚ) * ((2 * m + x + 1 + y).choose (2 * m + x + 1) : ℚ)
      else 0 := by
  rw [R_pow, Bpow, coeff_zonly_mul]
  simp_rw [coeff_Q]
  split_ifs with hx
  · obtain ⟨r, rfl⟩ := hx
    have hr : (r + r) / 2 = r := by omega
    simp only [hr]
    have hsum : ∑ t ∈ range (y + 1), PowerSeries.coeff t (inv1 1 ^ (m + 1)) *
        (((m + r).choose m : ℚ) * PowerSeries.coeff (y - t) (inv1 1 ^ r)) =
        ((m + r).choose m : ℚ) * PowerSeries.coeff y (inv1 1 ^ (m + 1) * inv1 1 ^ r) := by
      rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
        (fun i k ↦ PowerSeries.coeff i (inv1 1 ^ (m + 1)) * PowerSeries.coeff k (inv1 1 ^ r)), mul_sum]
      refine sum_congr rfl fun t _ ↦ ?_
      ring
    rw [hsum, ← pow_add, show m + 1 + r = (m + r) + 1 by ring, inv1_one_pow, coeff_inv1]
    congr 3 <;> ring
  · simp

end Abdesselam
