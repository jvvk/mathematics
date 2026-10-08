import AlternatingSum.Step1
import Mathlib.RingTheory.MvPowerSeries.Substitution
import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.RingTheory.MvPowerSeries.Inverse

/-!
  Steps 2 and 4 of the paper, in the ring `ℚ⟦w, z⟧` (`w = X 0`, `z = X 1`).
  `R = 1/((1-z)² - w²)`. With `α = z - w` and `β = z + w`, `(1-z)² - w² = (1-α)(1-β)`, so
  `R^(m+1)` is the substitution of `α, β` into `G_m = (1-X₀)^-(m+1) (1-X₁)^-(m+1)`, whose
  coefficients are `C(m+s,s) C(m+j,j)` (Step 4). The coefficient of `w^a z^b` in `α^s β^j` is
  `Σ_k (-1)^k C(s,k) C(j,a-k)` when `s + j = a + b` and `0` otherwise (Step 2).
-/

namespace Abdesselam

open MvPowerSeries Finset

/-- Power series in `w = X 0` and `z = X 1`. -/
abbrev PS := MvPowerSeries (Fin 2) ℚ

/-- `(1-z)² - w²`. -/
noncomputable def E : PS := (1 - X 1) ^ 2 - X 0 ^ 2

/-- `R = 1/((1-z)² - w²)`. -/
noncomputable def R : PS := E⁻¹

theorem constantCoeff_E : constantCoeff E = 1 := by simp [E]

theorem R_mul_E : R * E = 1 :=
  MvPowerSeries.inv_mul_cancel _ (by rw [constantCoeff_E]; norm_num)

/-- The substitution `X 0 ↦ α = z - w`, `X 1 ↦ β = z + w`. -/
noncomputable def ab : Fin 2 → PS := ![X 1 - X 0, X 1 + X 0]

theorem hab : HasSubst ab :=
  hasSubst_of_constantCoeff_zero fun s ↦ by fin_cases s <;> simp [ab]

/-- `Σ_n C(m+n, m) t^n = (1-t)^-(m+1)`. -/
noncomputable def inv1 (m : ℕ) : PowerSeries ℚ := PowerSeries.mk fun n ↦ ((m + n).choose m : ℚ)

/-- `G_m = (1-X₀)^-(m+1) (1-X₁)^-(m+1)`. -/
noncomputable def G (m : ℕ) : PS :=
  PowerSeries.subst (X 0 : PS) (inv1 m) * PowerSeries.subst (X 1 : PS) (inv1 m)

theorem subst_inv1_mul (m : ℕ) (t : Fin 2) :
    PowerSeries.subst (X t : PS) (inv1 m) * (1 - X t) ^ (m + 1) = 1 := by
  have h := congrArg (PowerSeries.substAlgHom (PowerSeries.HasSubst.X (S := ℚ) t))
    (PowerSeries.mk_add_choose_mul_one_sub_pow_eq_one (S := ℚ) (d := m))
  simp only [map_mul, map_pow, map_sub, map_one, PowerSeries.substAlgHom_X,
    PowerSeries.coe_substAlgHom] at h
  exact h

theorem G_mul (m : ℕ) : G m * ((1 - X 0) * (1 - X 1)) ^ (m + 1) = 1 := by
  rw [G, mul_pow]
  calc _ = (PowerSeries.subst (X 0 : PS) (inv1 m) * (1 - X 0) ^ (m + 1)) *
        (PowerSeries.subst (X 1 : PS) (inv1 m) * (1 - X 1) ^ (m + 1)) := by ring
    _ = 1 := by rw [subst_inv1_mul, subst_inv1_mul, one_mul]

/-- Step 4: substituting `α = z - w`, `β = z + w` into `G_m` gives `R^(m+1)`. -/
theorem subst_G (m : ℕ) : subst ab (G m) = R ^ (m + 1) := by
  have h := congrArg (substAlgHom (R := ℚ) hab) (G_mul m)
  simp only [map_mul, map_pow, map_sub, map_one, substAlgHom_X, coe_substAlgHom] at h
  have hE : (1 - ab 0) * (1 - ab 1) = E := by simp [ab, E]; ring
  rw [hE] at h
  calc subst ab (G m) = subst ab (G m) * (R * E) ^ (m + 1) := by rw [R_mul_E, one_pow, mul_one]
    _ = R ^ (m + 1) * (subst ab (G m) * E ^ (m + 1)) := by ring
    _ = R ^ (m + 1) := by rw [h, mul_one]

/-- The monomial exponent of `w^x z^y`. -/
noncomputable abbrev mono (x y : ℕ) : Fin 2 →₀ ℕ := Finsupp.single 0 x + Finsupp.single 1 y

@[simp] theorem mono_zero (x y : ℕ) : mono x y 0 = x := by simp [mono]
@[simp] theorem mono_one (x y : ℕ) : mono x y 1 = y := by simp [mono]

theorem mono_self (d : Fin 2 →₀ ℕ) : mono (d 0) (d 1) = d := by
  ext t; fin_cases t <;> simp

theorem mono_inj {x y x' y' : ℕ} : mono x y = mono x' y' ↔ x = x' ∧ y = y' := by
  constructor
  · intro h; exact ⟨by simpa using congrArg (· 0) h, by simpa using congrArg (· 1) h⟩
  · rintro ⟨rfl, rfl⟩; rfl

/-- The coefficients of `G_m` are `C(m+s, m) C(m+j, m)`. -/
theorem coeff_G (m : ℕ) (d : Fin 2 →₀ ℕ) :
    coeff d (G m) = ((m + d 0).choose m : ℚ) * ((m + d 1).choose m : ℚ) := by
  classical
  rw [G, coeff_mul, sum_eq_single_of_mem (Finsupp.single 0 (d 0), Finsupp.single 1 (d 1))]
  · simp [PowerSeries.coeff_subst_single, inv1]
  · simp only [mem_antidiagonal]; exact mono_self d
  · rintro ⟨p, q⟩ hpq hne
    simp only [mem_antidiagonal] at hpq
    simp only [PowerSeries.coeff_subst_single]
    by_cases hp : p = Finsupp.single 0 (p 0)
    · by_cases hq : q = Finsupp.single 1 (q 1)
      · exfalso; apply hne
        have h0 : p 0 = d 0 := by
          rw [← hpq, hp, hq]; simp
        have h1 : q 1 = d 1 := by
          rw [← hpq, hp, hq]; simp
        rw [hp, hq, h0, h1]
      · simp [hq]
    · simp [hp]

/-- `H = Σ_m (-1)^(ν-m) C(ν,m) G_(u+m)`, whose substitution is `R^(u+1) (R-1)^ν`. -/
noncomputable def H (u ν : ℕ) : PS :=
  ∑ m ∈ range (ν + 1), ((-1 : ℚ) ^ (ν - m) * (ν.choose m : ℚ)) • G (u + m)

theorem subst_H (u ν : ℕ) : subst ab (H u ν) = R ^ (u + 1) * (R - 1) ^ ν := by
  rw [← coe_substAlgHom (R := ℚ) hab, H, map_sum]
  simp only [map_smul, coe_substAlgHom, subst_G]
  rw [sub_eq_add_neg, add_pow, mul_sum]
  refine sum_congr rfl fun m _ ↦ ?_
  rw [Algebra.smul_def]
  simp only [map_mul, map_pow, map_neg, map_one, map_natCast]
  rw [show u + m + 1 = (u + 1) + m by ring, pow_add]
  ring

/-- The coefficients of `H` are the alternating sums `c_{s,j}` of Step 3. -/
theorem coeff_H (u ν : ℕ) (d : Fin 2 →₀ ℕ) : coeff d (H u ν) = c u ν (d 0) (d 1) := by
  rw [H, map_sum, c, ← sum_range_reflect]
  refine sum_congr rfl fun p hp ↦ ?_
  have hp := mem_range.1 hp
  rw [coeff_smul, coeff_G]
  have e1 : ν - (ν + 1 - 1 - p) = p := by omega
  have e2 : u + (ν + 1 - 1 - p) = u + ν - p := by omega
  have e3 : ν.choose (ν + 1 - 1 - p) = ν.choose p := by
    rw [show ν + 1 - 1 - p = ν - p by omega, Nat.choose_symm (by omega)]
  rw [e1, e2, e3, Nat.choose_symm_add, Nat.choose_symm_add]
  ring

/-- `P_s = [t^a] (1-t)^s (1+t)^j = Σ_k (-1)^k C(s,k) C(j,a-k)` (Step 1). -/
def P (s j a : ℕ) : ℚ := ∑ k ∈ range (a + 1), (-1) ^ k * (s.choose k : ℚ) * (j.choose (a - k) : ℚ)

/-- The binomial theorem for `z + c w` as a sum of monomials. -/
theorem pow_expand (r : ℚ) (n : ℕ) :
    (X 1 + C r * X 0 : PS) ^ n =
      ∑ k ∈ range (n + 1), monomial (mono k (n - k)) (r ^ k * (n.choose k : ℚ)) := by
  rw [add_comm, add_pow]
  refine sum_congr rfl fun k _ ↦ ?_
  rw [mul_pow, ← map_pow, X_pow_eq, X_pow_eq, ← monomial_zero_eq_C_apply, ← map_natCast (C (σ := Fin 2)),
    ← monomial_zero_eq_C_apply, monomial_mul_monomial, monomial_mul_monomial, monomial_mul_monomial]
  simp [mono]

theorem mono_add (x y x' y' : ℕ) : mono x y + mono x' y' = mono (x + x') (y + y') := by
  ext t; fin_cases t <;> simp

/-- Throwing away the terms `k > s` (where `C(s,k) = 0`) of a sum cut at `k ≤ a`. -/
theorem sum_trunc (s a : ℕ) (F : ℕ → ℚ) (hF : ∀ k, s < k → F k = 0) :
    ∑ k ∈ range (s + 1), (if k ≤ a then F k else 0) = ∑ k ∈ range (a + 1), F k := by
  have h1 : ∑ k ∈ range (s + 1), (if k ≤ a then F k else 0) =
      ∑ k ∈ range (s + a + 1), (if k ≤ a then F k else 0) := by
    refine sum_subset (by intro k; simp only [mem_range]; omega) fun k hk hk' ↦ ?_
    simp only [mem_range] at hk hk'
    rw [hF k (by omega), ite_self]
  have h2 : range (a + 1) = (range (s + a + 1)).filter (· ≤ a) := by
    ext k; simp only [mem_range, mem_filter]; omega
  rw [h1, h2, sum_filter]

/-- Step 2: the coefficient of `w^a z^b` in `α^s β^j` (homogeneous of degree `s + j`). -/
theorem coeff_alpha_beta (s j a b : ℕ) :
    coeff (mono a b) ((X 1 - X 0) ^ s * (X 1 + X 0) ^ j : PS) =
      if s + j = a + b then P s j a else 0 := by
  have hα : (X 1 - X 0 : PS) = X 1 + C (-1) * X 0 := by simp [sub_eq_add_neg]
  have hβ : (X 1 + X 0 : PS) = X 1 + C 1 * X 0 := by simp
  rw [hα, hβ, pow_expand, pow_expand, sum_mul_sum, map_sum]
  simp only [monomial_mul_monomial, mono_add, map_sum, coeff_monomial, mono_inj, one_pow, one_mul]
  split_ifs with hab'
  · have hcond : ∀ k ∈ range (s + 1), ∀ t ∈ range (j + 1),
        (a = k + t ∧ b = s - k + (j - t)) ↔ (t = a - k ∧ k ≤ a) := by
      intro k hk t ht; simp only [mem_range] at hk ht; omega
    have hin : ∀ k ∈ range (s + 1), (∑ t ∈ range (j + 1),
        if a = k + t ∧ b = s - k + (j - t) then (-1) ^ k * (s.choose k : ℚ) * (j.choose t : ℚ)
          else 0) = if k ≤ a then (-1) ^ k * (s.choose k : ℚ) * (j.choose (a - k) : ℚ) else 0 := by
      intro k hk
      rw [sum_congr rfl fun t ht ↦ by rw [if_congr (hcond k hk t ht) rfl rfl]]
      by_cases hka : k ≤ a
      · simp only [hka, and_true, ite_true]
        rw [sum_ite_eq']
        split_ifs with hm
        · rfl
        · simp only [mem_range, not_lt] at hm
          simp [Nat.choose_eq_zero_of_lt (by omega : j < a - k)]
      · simp [hka]
    rw [sum_congr rfl hin, P]
    exact sum_trunc s a _ fun k hk ↦ by rw [Nat.choose_eq_zero_of_lt hk, Nat.cast_zero, mul_zero, zero_mul]
  · refine sum_eq_zero fun k hk ↦ sum_eq_zero fun t ht ↦ ?_
    simp only [mem_range] at hk ht
    rw [ite_eq_right (by omega)]

/-- Steps 2 and 4 combined: the coefficient of `w^a z^b` in `F(z-w, z+w)` is
`Σ_{s+j = a+b} [α^s β^j] F · P_s`. -/
theorem coeff_subst_ab (F : PS) (a b : ℕ) :
    coeff (mono a b) (subst ab F) =
      ∑ s ∈ range (a + b + 1), coeff (mono s (a + b - s)) F * P s (a + b - s) a := by
  classical
  rw [coeff_subst hab]
  have hterm : ∀ d : Fin 2 →₀ ℕ, coeff d F • coeff (mono a b) (d.prod fun t e ↦ ab t ^ e) =
      coeff d F * (if d 0 + d 1 = a + b then P (d 0) (d 1) a else 0) := by
    intro d
    rw [Finsupp.prod_fintype _ _ (by simp), Fin.prod_univ_two, smul_eq_mul]
    simp only [ab, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    rw [coeff_alpha_beta]
  simp_rw [hterm]
  rw [finsum_eq_sum_of_support_subset (s := (range (a + b + 1)).image fun s ↦ mono s (a + b - s))]
  · rw [sum_image]
    · refine sum_congr rfl fun s hs ↦ ?_
      have hs := mem_range.1 hs
      simp only [mono_zero, mono_one]
      rw [ite_eq_left (by omega)]
    · intro x hx y hy hxy
      exact (mono_inj.1 hxy).1
  · intro d hd
    rw [Function.mem_support] at hd
    have h : d 0 + d 1 = a + b := by
      by_contra h; apply hd; rw [ite_eq_right h, mul_zero]
    simp only [coe_image, coe_range, Set.mem_image, Set.mem_Iio]
    refine ⟨d 0, ?_, ?_⟩
    · omega
    · conv_rhs => rw [← mono_self d]
      congr 1
      omega

end Abdesselam
