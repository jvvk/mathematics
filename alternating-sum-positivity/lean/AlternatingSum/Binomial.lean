import AlternatingSum.Taylor

/-!
  The binomial-basis form of Theorem 1 and Taylor's conjectured formula (MathOverflow 498232):
  `L = (u+ν)!²/ν! Σ_m C(u,m) [w^a z^b] R (R-1)^(m+ν)`, and for even `a` the inner coefficient
  `[w^a z^b] R (R-1)^k` equals Taylor's inner sum
  `Σ_{⌈b/2⌉ ≤ d ≤ b} (-1)^(b-d) 2^(2d-b) C(d, 2d-b) C(a/2+d, d) C(a/2+d, k)`.
  Route: `R (R-1)^k = (1-E)^k / E^(k+1) = Σ_N C(N,k) (1-E)^N` with `1 - E = w² + (2z - z²)`.
-/

namespace Abdesselam

open MvPowerSeries Finset Nat

/-- **Binomial-basis form** of Theorem 1. -/
theorem binomial_basis (u a b n : ℕ) (hn : n ≤ a + b) :
    L u a b n = ((u + (a + b - n)) ! : ℚ) ^ 2 / ((a + b - n) ! : ℚ) *
      ∑ m ∈ range (u + 1), (u.choose m : ℚ) * coeff (mono a b) (R * (R - 1) ^ (m + (a + b - n))) := by
  rw [main u a b n hn]
  congr 1
  have h : R ^ (u + 1) = ∑ m ∈ range (u + 1), (u.choose m : ℚ) • (R * (R - 1) ^ m) := by
    calc R ^ (u + 1) = R * ((R - 1) + 1) ^ u := by rw [sub_add_cancel, _root_.pow_succ']
      _ = R * ∑ m ∈ range (u + 1), (R - 1) ^ m * 1 ^ (u - m) * (u.choose m : PS) := by
        rw [add_pow]
      _ = _ := by
        rw [mul_sum]
        refine sum_congr rfl fun m _ ↦ ?_
        rw [Algebra.smul_def, map_natCast, one_pow, mul_one]; ring
  rw [h, sum_mul, map_sum]
  refine sum_congr rfl fun m _ ↦ ?_
  rw [smul_mul_assoc, coeff_smul, mul_assoc R, ← pow_add]

/-- Coefficients of a series in `z` only. -/
theorem coeff_zonly (g : PowerSeries ℚ) (x y : ℕ) :
    coeff (mono x y) (PowerSeries.subst (X 1 : PS) g) = if x = 0 then PowerSeries.coeff y g else 0 := by
  classical
  rw [PowerSeries.coeff_subst_single]
  simp only [mono_one]
  congr 1
  apply propext
  constructor
  · intro h; simpa using congrArg (· 0) h
  · rintro rfl; exact mono_zero_left y

/-- `2t - t²`. -/
noncomputable def vpoly : PowerSeries ℚ := PowerSeries.X * (2 - PowerSeries.X)

theorem one_sub_E : 1 - E = X 0 ^ 2 + PowerSeries.subst (X 1 : PS) vpoly := by
  have hv : PowerSeries.subst (X 1 : PS) vpoly = X 1 * (2 - X 1) := by
    rw [← PowerSeries.coe_substAlgHom (PowerSeries.HasSubst.X (S := ℚ) (1 : Fin 2)), vpoly]
    simp only [map_mul, map_sub, map_ofNat, PowerSeries.substAlgHom_X]
  rw [hv, E]
  ring

/-- `(2 - t)^d = Σ_j (-1)^j 2^(d-j) C(d,j) t^j`. -/
theorem two_sub_pow (d : ℕ) :
    ((2 : PowerSeries ℚ) - PowerSeries.X) ^ d = ∑ j ∈ range (d + 1),
      PowerSeries.C ((-1) ^ j * 2 ^ (d - j) * (d.choose j : ℚ)) * PowerSeries.X ^ j := by
  rw [sub_eq_add_neg, add_comm, add_pow]
  refine sum_congr rfl fun j _ ↦ ?_
  rw [map_mul, map_mul, map_pow, map_pow, map_neg, map_one, map_natCast, map_ofNat, neg_pow]
  ring

/-- `[t^e] (2 - t)^d = (-1)^e 2^(d-e) C(d,e)`. -/
theorem coeff_two_sub_pow (d e : ℕ) :
    PowerSeries.coeff e (((2 : PowerSeries ℚ) - PowerSeries.X) ^ d) =
      (-1) ^ e * 2 ^ (d - e) * (d.choose e : ℚ) := by
  rw [two_sub_pow, map_sum]
  simp_rw [PowerSeries.coeff_C_mul_X_pow]
  rw [sum_ite_eq]
  split_ifs with he
  · rfl
  · simp only [mem_range, not_lt] at he
    rw [Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero, mul_zero]

theorem coeff_vpoly_pow (d b : ℕ) :
    PowerSeries.coeff b (vpoly ^ d) =
      if d ≤ b then (-1) ^ (b - d) * 2 ^ (d - (b - d)) * (d.choose (b - d) : ℚ) else 0 := by
  rw [vpoly, mul_pow, PowerSeries.coeff_X_pow_mul']
  split_ifs
  · rw [coeff_two_sub_pow]
  · rfl

theorem coeff_one_sub_E_pow (N a b : ℕ) :
    coeff (mono a b) ((1 - E) ^ N) =
      if Even a ∧ a / 2 ≤ N then (N.choose (a / 2) : ℚ) * PowerSeries.coeff b (vpoly ^ (N - a / 2))
      else 0 := by
  rw [one_sub_E, add_pow, map_sum]
  have hterm : ∀ i ∈ range (N + 1), coeff (mono a b)
      ((X 0 ^ 2) ^ i * PowerSeries.subst (X 1 : PS) vpoly ^ (N - i) * (N.choose i : PS)) =
      if a = 2 * i then (N.choose i : ℚ) * PowerSeries.coeff b (vpoly ^ (N - i)) else 0 := by
    intro i _
    rw [← map_natCast (C (σ := Fin 2) (R := ℚ)), mul_comm, coeff_C_mul, ← pow_mul,
      ← PowerSeries.subst_pow (PowerSeries.HasSubst.X 1), coeff_wpow_mul, coeff_zonly]
    by_cases ha : a = 2 * i
    · rw [ite_eq_left (by omega), ite_eq_left (by omega), ite_eq_left ha]
    · rw [ite_eq_right ha]
      split_ifs <;> first | omega | simp
  rw [sum_congr rfl hterm]
  split_ifs with h
  · obtain ⟨⟨r, hr⟩, hN⟩ := h
    rw [sum_eq_single (a / 2)]
    · rw [ite_eq_left (by omega)]
    · intro i _ hi; rw [ite_eq_right (by omega)]
    · intro hi; simp only [mem_range] at hi; omega
  · refine sum_eq_zero fun i hi ↦ ?_
    simp only [mem_range] at hi
    rw [ite_eq_right]
    intro ha; exact h ⟨⟨i, by omega⟩, by omega⟩

/-- `R (R-1)^k = (1-E)^k / E^(k+1)`, the substitution of `1 - E` into `t^k/(1-t)^(k+1)`. -/
theorem R_mul_pow (k : ℕ) :
    R * (R - 1) ^ k = PowerSeries.subst (1 - E) (PowerSeries.X ^ k * inv1 k) := by
  have ha : PowerSeries.HasSubst (1 - E) :=
    PowerSeries.HasSubst.of_constantCoeff_zero (by rw [map_sub, map_one, constantCoeff_E, sub_self])
  have hS := subst_inv1_mul' k (1 - E) ha
  rw [sub_sub_cancel] at hS
  have hsplit : PowerSeries.subst (1 - E) (PowerSeries.X ^ k * inv1 k) =
      (1 - E) ^ k * PowerSeries.subst (1 - E) (inv1 k) := by
    rw [PowerSeries.subst_mul ha, PowerSeries.subst_pow ha, PowerSeries.subst_X ha]
  have hR1 : R - 1 = R * (1 - E) := by rw [mul_sub, mul_one, R_mul_E]
  rw [hsplit, hR1, mul_pow]
  calc R * (R ^ k * (1 - E) ^ k) = R * (R ^ k * (1 - E) ^ k) *
        (PowerSeries.subst (1 - E) (inv1 k) * E ^ (k + 1)) := by rw [hS, mul_one]
    _ = (R * E) ^ (k + 1) * ((1 - E) ^ k * PowerSeries.subst (1 - E) (inv1 k)) := by ring
    _ = _ := by rw [R_mul_E, one_pow, one_mul]

/-- The coefficient of `w^a z^b` in `R (R-1)^k` as a finite sum over `d = N - a/2`. -/
theorem coeff_R_mul_pow (k a b : ℕ) (ha : Even a) :
    coeff (mono a b) (R * (R - 1) ^ k) = ∑ d ∈ range (b + 1),
      ((a / 2 + d).choose k : ℚ) * ((a / 2 + d).choose (a / 2) : ℚ) *
        PowerSeries.coeff b (vpoly ^ d) := by
  have hS : PowerSeries.HasSubst (1 - E) :=
    PowerSeries.HasSubst.of_constantCoeff_zero (by rw [map_sub, map_one, constantCoeff_E, sub_self])
  rw [R_mul_pow, PowerSeries.coeff_subst hS]
  have hterm : ∀ N : ℕ, PowerSeries.coeff N (PowerSeries.X ^ k * inv1 k) • coeff (mono a b) ((1 - E) ^ N)
      = if a / 2 ≤ N then (N.choose k : ℚ) * ((N.choose (a / 2) : ℚ) *
          PowerSeries.coeff b (vpoly ^ (N - a / 2))) else 0 := by
    intro N
    rw [coeff_one_sub_E_pow, PowerSeries.coeff_X_pow_mul', smul_eq_mul]
    by_cases hN : a / 2 ≤ N
    · have hc : (if k ≤ N then PowerSeries.coeff (N - k) (inv1 k) else 0) = (N.choose k : ℚ) := by
        split_ifs with hk
        · rw [coeff_inv1, Nat.add_sub_cancel' hk]
        · rw [Nat.choose_eq_zero_of_lt (by omega)]; simp
      rw [hc, ite_eq_left (show Even a ∧ a / 2 ≤ N from ⟨ha, hN⟩), ite_eq_left hN]
    · rw [ite_eq_right (fun h : Even a ∧ a / 2 ≤ N ↦ hN h.2), ite_eq_right hN, mul_zero]
  simp_rw [hterm]
  rw [finsum_eq_sum_of_support_subset (s := (range (b + 1)).map (addLeftEmbedding (a / 2)))]
  · rw [sum_map]
    refine sum_congr rfl fun d _ ↦ ?_
    simp only [addLeftEmbedding_apply, le_add_iff_nonneg_right, Nat.zero_le, ite_true,
      Nat.add_sub_cancel_left]
    ring
  · intro N hN
    rw [Function.mem_support] at hN
    simp only [coe_map, coe_range, Set.mem_image, Set.mem_Iio, addLeftEmbedding_apply]
    by_cases h1 : a / 2 ≤ N
    · refine ⟨N - a / 2, ?_, by omega⟩
      by_contra h2
      apply hN
      rw [ite_eq_left h1, coeff_vpoly_pow, ite_eq_right (by omega), mul_zero, mul_zero]
    · exact absurd (by rw [ite_eq_right h1]) hN

/-- Taylor's inner sum, as written on MathOverflow (`a` even). -/
def Tinner (a b n m : ℕ) : ℚ :=
  ∑ d ∈ Icc ((b + 1) / 2) b, (-1) ^ (b - d) * 2 ^ (2 * d - b) * (d.choose (2 * d - b) : ℚ) *
    ((a / 2 + d).choose d : ℚ) * ((a / 2 + d).choose (m + a + b - n) : ℚ)

/-- The inner coefficients of the binomial-basis form are Taylor's inner sums. -/
theorem inner_eq_Tinner (a b n m : ℕ) (ha : Even a) (hn : n ≤ a + b) :
    coeff (mono a b) (R * (R - 1) ^ (m + (a + b - n))) = Tinner a b n m := by
  rw [coeff_R_mul_pow _ a b ha, Tinner]
  symm
  rw [← sum_subset (s₁ := Icc ((b + 1) / 2) b) (s₂ := range (b + 1))]
  · refine sum_congr rfl fun d hd ↦ ?_
    simp only [mem_Icc] at hd
    rw [coeff_vpoly_pow, ite_eq_left hd.2, show d - (b - d) = 2 * d - b by omega,
      show m + a + b - n = m + (a + b - n) by omega, Nat.choose_symm_add,
      ← Nat.choose_symm (show b - d ≤ d by omega), show d - (b - d) = 2 * d - b by omega]
    ring
  · intro d hd; simp only [mem_Icc, mem_range] at hd ⊢; omega
  · intro d hd hd'
    simp only [mem_Icc, mem_range, not_and, not_le] at hd hd'
    rw [coeff_vpoly_pow]
    split_ifs
    · rw [Nat.choose_eq_zero_of_lt (show d < b - d by omega)]; simp
    · simp

/-- **Taylor's conjectured formula** (MathOverflow 498232), for even `a`. -/
theorem taylor_formula (u a b n : ℕ) (ha : Even a) (hn : n ≤ a + b) :
    L u a b n = ((u + (a + b - n)) ! : ℚ) ^ 2 / ((a + b - n) ! : ℚ) *
      ∑ m ∈ range (n + 1), (u.choose m : ℚ) * Tinner a b n m := by
  rw [binomial_basis u a b n hn]
  congr 1
  have hz : ∀ m, n < m → coeff (mono a b) (R * (R - 1) ^ (m + (a + b - n))) = 0 := by
    intro m hm
    have hR : R = R ^ (0 + 1) := by rw [zero_add, pow_one]
    have hw := Wt_mul (Wt_zero R) (Wt_pow Wt_R_sub_one (m + (a + b - n)))
    exact hw (mono a b) (by simp; omega)
  have e1 : ∑ m ∈ range (u + 1), (u.choose m : ℚ) * coeff (mono a b) (R * (R - 1) ^ (m + (a + b - n)))
      = ∑ m ∈ range (u + n + 1), (u.choose m : ℚ) *
          coeff (mono a b) (R * (R - 1) ^ (m + (a + b - n))) := by
    refine sum_subset (by intro m; simp only [mem_range]; omega) fun m hm hm' ↦ ?_
    simp only [mem_range, not_lt] at hm hm'
    rw [Nat.choose_eq_zero_of_lt (by omega)]; simp
  have e2 : ∑ m ∈ range (n + 1), (u.choose m : ℚ) * Tinner a b n m
      = ∑ m ∈ range (u + n + 1), (u.choose m : ℚ) *
          coeff (mono a b) (R * (R - 1) ^ (m + (a + b - n))) := by
    have hs := sum_subset (s₁ := range (n + 1)) (s₂ := range (u + n + 1))
      (f := fun m ↦ (u.choose m : ℚ) * coeff (mono a b) (R * (R - 1) ^ (m + (a + b - n))))
      (by intro m; simp only [mem_range]; omega)
      (fun m hm hm' ↦ by
        simp only [mem_range, not_lt] at hm hm'
        rw [hz m (by omega), mul_zero])
    rw [← hs]
    exact sum_congr rfl fun m _ ↦ by rw [inner_eq_Tinner a b n m ha hn]
  rw [e1, e2]

end Abdesselam
