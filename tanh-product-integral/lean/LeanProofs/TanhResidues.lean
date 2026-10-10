import Mathlib

/-!
# Residues of `∏ (1 - q^k)/(1 + q^k)` at roots of unity (MSE 5150767)

`P_n(q) = ∏_{k ≤ n} (1 - q^k)/(1 + q^k)` has its poles at the primitive `2m`-th roots `ζ = e^{iπj/m}` with
`⌊n/m⌋` odd. The residue computation reduces to a product of tangents of the angles `x_k = π j k / (2m)`.
This file proves the finite identities it uses; `j` is odd and coprime to `m` throughout.

* `const_identity`: the factors with `ζ^k = ±1` give `(2/m) 4^e e!² / (2e+1)!`.
* `factor_identity`: `(1 - e^{iθ}) / (1 + e^{iθ}) = -i tan(θ/2)`.
* `tan_pair`, `tan_refl`, `tan_tail`: `tan x_{m-k} = (tan x_k)⁻¹`, `tan x_{2m-k} = -tan x_k`,
  `tan x_{m+k} = -(tan x_k)⁻¹`.
* `prod_tan`: `∏_{k=1}^{m-1} tan x_k = ε_m(j)` (`1` for odd `m`, `χ₋₄(j)` for even `m`).
* `period_prod`: a full period of the factors `-i tan x_k` (`k ≠ m`) multiplies to `1`.
* `cot_symm`: `∏_{k ≤ ρ} cot x_k = ε_m(j) ∏_{k ≤ m-1-ρ} cot x_k`, so only `ρ' = min(ρ, m-1-ρ)` matters.
* `residue_product`: over the non-multiples `k ≤ n = (2e+1)m + ρ` of `m`, the factors `-i tan x_k` multiply to
  `(-i)^{m-1} ε_m(j) ∏_{k ≤ ρ} i cot x_k` (full periods give `1`).
* `inv_symm`: `P_n(1/q) = (-1)^n P_n(q)`.
-/

namespace TanhResidues

open Real Finset

/-! ### The constant -/

/-- The `e + 1` factors with `k = (2i+1) m` contribute `2/k` and the `e` factors with `k = 2im` contribute `k/2`. -/
theorem const_identity (m : ℚ) (hm : m ≠ 0) (e : ℕ) :
    (∏ i ∈ range (e + 1), (2 / ((2 * i + 1) * m))) * (∏ i ∈ range e, ((2 * (i + 1) * m) / 2)) =
      2 / m * 4 ^ e * (e.factorial : ℚ) ^ 2 / (2 * e + 1).factorial := by
  induction e with
  | zero => simp
  | succ e ih =>
    rw [prod_range_succ (fun i : ℕ => (2 : ℚ) / ((2 * i + 1) * m)) (e + 1),
      prod_range_succ (fun i : ℕ => (2 * ((i : ℚ) + 1) * m) / 2) e]
    calc (∏ i ∈ range (e + 1), (2 : ℚ) / ((2 * i + 1) * m)) * (2 / ((2 * ((e + 1 : ℕ) : ℚ) + 1) * m)) *
          ((∏ i ∈ range e, (2 * ((i : ℚ) + 1) * m) / 2) * ((2 * ((e : ℚ) + 1) * m) / 2))
        = ((∏ i ∈ range (e + 1), (2 : ℚ) / ((2 * i + 1) * m)) *
            (∏ i ∈ range e, (2 * ((i : ℚ) + 1) * m) / 2)) *
            ((2 / ((2 * ((e + 1 : ℕ) : ℚ) + 1) * m)) * ((2 * ((e : ℚ) + 1) * m) / 2)) := by ring
      _ = 2 / m * 4 ^ (e + 1) * ((e + 1).factorial : ℚ) ^ 2 / (2 * (e + 1) + 1).factorial := by
        rw [ih, show 2 * (e + 1) + 1 = ((2 * e + 1) + 1) + 1 by ring, Nat.factorial_succ (2 * e + 1 + 1),
          Nat.factorial_succ (2 * e + 1), Nat.factorial_succ e]
        have h1 : ((2 * e + 1).factorial : ℚ) ≠ 0 := by positivity
        push_cast
        field_simp
        ring

/-! ### One factor at a root of unity -/

/-- `(1 - e^{iθ}) / (1 + e^{iθ}) = -i tan(θ/2)`. -/
theorem factor_identity (θ : ℝ) (h : Real.cos (θ / 2) ≠ 0) :
    (1 - Complex.exp (θ * Complex.I)) / (1 + Complex.exp (θ * Complex.I)) =
      -Complex.I * (Real.tan (θ / 2) : ℂ) := by
  set z : ℂ := ((θ / 2 : ℝ) : ℂ) with hz
  set w := Complex.exp (z * Complex.I) with hwdef
  have hw : w ≠ 0 := Complex.exp_ne_zero _
  have hx : Complex.exp (θ * Complex.I) = w ^ 2 := by
    rw [hwdef, ← Complex.exp_nat_mul]; congr 1; rw [hz]; push_cast; ring
  have hneg : Complex.exp (-z * Complex.I) = w⁻¹ := by rw [neg_mul, Complex.exp_neg]
  have hc : Complex.cos z ≠ 0 := by rw [hz, ← Complex.ofReal_cos]; exact_mod_cast h
  have hcw : Complex.cos z = (w + w⁻¹) / 2 := by rw [Complex.cos, hneg]
  have hsw : Complex.sin z = (w⁻¹ - w) * Complex.I / 2 := by rw [Complex.sin, hneg]
  have hden : 1 + w ^ 2 ≠ 0 := by
    intro h0; apply hc; rw [hcw]; field_simp; linear_combination h0
  rw [Complex.ofReal_tan, ← hz, Complex.tan, hsw, hcw, hx]
  have hwi : w + w⁻¹ ≠ 0 := by intro h0; apply hc; rw [hcw, h0, zero_div]
  field_simp
  ring_nf
  rw [Complex.I_sq]
  field_simp
  ring

/-! ### Tangents of `x_k = π j k / (2m)` -/

/-- The angle `π j k / (2m)`. -/
noncomputable def ang (m j : ℕ) (k : ℤ) : ℝ := π * j * k / (2 * m)

theorem tan_add_int_pi (x : ℝ) (n : ℤ) : Real.tan (x + n * π) = Real.tan x := (Real.tan_periodic.int_mul n) x

/-- `tan(π/2 + x) = -(tan x)⁻¹` (total, with `0⁻¹ = 0`). -/
theorem tan_pi_div_two_add' (x : ℝ) : Real.tan (π / 2 + x) = -(Real.tan x)⁻¹ := by
  rw [show π / 2 + x = π / 2 - (-x) by ring, Real.tan_pi_div_two_sub, Real.tan_neg, inv_neg]

/-- Pairing `k ↔ m - k`: for odd `j`, `tan x_{m-k} = (tan x_k)⁻¹`. -/
theorem tan_pair (m j : ℕ) (hm : m ≠ 0) (hj : Odd j) (k : ℤ) :
    Real.tan (ang m j (m - k)) = (Real.tan (ang m j k))⁻¹ := by
  obtain ⟨r, rfl⟩ := hj
  have : ang m (2 * r + 1) (m - k) = π / 2 - ang m (2 * r + 1) k + (r : ℤ) * π := by
    unfold ang; field_simp; push_cast; ring
  rw [this, tan_add_int_pi, Real.tan_pi_div_two_sub]

/-- Reflection `k ↔ 2m - k`: `tan x_{2m-k} = -tan x_k`. -/
theorem tan_refl (m j : ℕ) (hm : m ≠ 0) (k : ℤ) :
    Real.tan (ang m j (2 * m - k)) = -Real.tan (ang m j k) := by
  have : ang m j (2 * m - k) = -ang m j k + (j : ℤ) * π := by unfold ang; field_simp; push_cast; ring
  rw [this, tan_add_int_pi, Real.tan_neg]

/-- The tail `k ↦ m + k`: for odd `j`, `tan x_{m+k} = -(tan x_k)⁻¹`. -/
theorem tan_tail (m j : ℕ) (hm : m ≠ 0) (hj : Odd j) (k : ℤ) :
    Real.tan (ang m j (m + k)) = -(Real.tan (ang m j k))⁻¹ := by
  obtain ⟨r, rfl⟩ := hj
  have : ang m (2 * r + 1) (m + k) = π / 2 + ang m (2 * r + 1) k + (r : ℤ) * π := by
    unfold ang; field_simp; push_cast; ring
  rw [this, tan_add_int_pi, tan_pi_div_two_add']

/-- For `0 < k < m` and `j` coprime to `m`, `tan x_k ≠ 0`. -/
theorem tan_ne_zero (m j : ℕ) (hj : Nat.Coprime j m) (k : ℕ) (hk0 : 0 < k) (hkm : k < m) :
    Real.tan (ang m j k) ≠ 0 := by
  intro h
  rw [Real.tan_eq_zero_iff] at h
  obtain ⟨n, hn⟩ := h
  have hm : (m : ℝ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
  have h2 : ((j * k : ℕ) : ℝ) = ((n * m : ℤ) : ℝ) := by
    unfold ang at hn; field_simp at hn; simp only [Int.cast_natCast] at hn; push_cast; linarith [hn]
  have h3 : ((j * k : ℕ) : ℤ) = n * m := by exact_mod_cast h2
  have hdvd : (m : ℤ) ∣ ((j * k : ℕ) : ℤ) := ⟨n, by rw [h3]; ring⟩
  have : m ∣ j * k := Int.natCast_dvd_natCast.mp hdvd
  have : m ∣ k := (Nat.Coprime.symm hj).dvd_of_dvd_mul_left this
  exact absurd (Nat.le_of_dvd hk0 this) (by omega)

/-- `ε_m(j)`: `1` for odd `m`, and `χ₋₄(j) = tan(π j / 4)` for even `m`. -/
noncomputable def eps (m j : ℕ) : ℝ := if Even m then Real.tan (π * j / 4) else 1

theorem tan_quarter (j : ℕ) (hj : Odd j) : Real.tan (π * j / 4) = if j % 4 = 1 then 1 else -1 := by
  obtain ⟨r, rfl⟩ := hj
  rcases Nat.even_or_odd r with ⟨s, rfl⟩ | ⟨s, rfl⟩
  · have : π * ((2 * (s + s) + 1 : ℕ) : ℝ) / 4 = π / 4 + (s : ℤ) * π := by push_cast; ring
    rw [this, tan_add_int_pi, Real.tan_pi_div_four, if_pos (by omega)]
  · have : π * ((2 * (2 * s + 1) + 1 : ℕ) : ℝ) / 4 = -(π / 4) + ((s + 1 : ℕ) : ℤ) * π := by push_cast; ring
    rw [this, tan_add_int_pi, Real.tan_neg, Real.tan_pi_div_four, if_neg (by omega)]

theorem eps_sq (m j : ℕ) (hj : Odd j) : eps m j * eps m j = 1 := by
  unfold eps; split_ifs
  · rw [tan_quarter j hj]; split_ifs <;> norm_num
  · norm_num

/-- `∏_{k=1}^{m-1} tan x_k = ε_m(j)`: pair `k` with `m - k`; for even `m` the middle term is `tan(π j / 4)`. -/
theorem prod_tan (m j : ℕ) (hm : m ≠ 0) (hj : Odd j) (hc : Nat.Coprime j m) :
    ∏ k ∈ Ioo 0 m, Real.tan (ang m j k) = eps m j := by
  -- Π² over the pairing equals Π · Π⁻¹ termwise, so we split the product at the middle.
  have hpair : ∀ k ∈ Ioo 0 m, Real.tan (ang m j k) * Real.tan (ang m j (m - k)) = 1 := by
    intro k hk
    rw [mem_Ioo] at hk
    rw [tan_pair m j hm hj k]
    exact mul_inv_cancel₀ (tan_ne_zero m j hc k hk.1 hk.2)
  rcases Nat.even_or_odd m with ⟨h, rfl⟩ | ⟨h, rfl⟩
  · -- m = 2h: split Ioo 0 (2h) = Ioo 0 h ∪ {h} ∪ Ioo h (2h)
    have hh : 0 < h := by omega
    have split : Ioo 0 (h + h) = Ioo 0 h ∪ ({h} ∪ Ioo h (h + h)) := by
      ext k; simp only [mem_Ioo, mem_union, mem_singleton]; omega
    have d1 : Disjoint (Ioo 0 h) ({h} ∪ Ioo h (h + h)) := by
      rw [disjoint_left]; intro k hk hk'; simp only [mem_Ioo, mem_union, mem_singleton] at hk hk'; omega
    have d2 : Disjoint ({h} : Finset ℕ) (Ioo h (h + h)) := by
      rw [disjoint_left]; intro k hk hk'; simp only [mem_Ioo, mem_singleton] at hk hk'; omega
    rw [split, prod_union d1, prod_union d2, prod_singleton]
    have refl : ∏ k ∈ Ioo h (h + h), Real.tan (ang (h + h) j k) =
        ∏ k ∈ Ioo 0 h, Real.tan (ang (h + h) j (((h + h : ℕ) : ℤ) - k)) := by
      refine prod_nbij' (fun k => h + h - k) (fun k => h + h - k) ?_ ?_ ?_ ?_ ?_
      · intro k hk; simp only [mem_coe, mem_Ioo] at hk ⊢; omega
      · intro k hk; simp only [mem_coe, mem_Ioo] at hk ⊢; omega
      · intro k hk; simp only [mem_coe, mem_Ioo] at hk; omega
      · intro k hk; simp only [mem_coe, mem_Ioo] at hk; omega
      · intro k hk
        simp only [mem_Ioo] at hk
        congr 1; push_cast [Nat.cast_sub (by omega : k ≤ h + h)]; ring
    have mid : Real.tan (ang (h + h) j h) = eps (h + h) j := by
      unfold eps ang; rw [if_pos ⟨h, rfl⟩]; congr 1
      have : (h : ℝ) ≠ 0 := by exact_mod_cast hh.ne'
      push_cast; field_simp; ring
    rw [refl, mid, mul_left_comm, ← prod_mul_distrib]
    rw [prod_congr rfl (fun k hk => hpair k (by simp only [mem_Ioo] at hk ⊢; omega)), prod_const_one, mul_one]
  · -- m = 2h + 1: split Ioo 0 (2h+1) = Ioo 0 (h+1) ∪ Ioo h (2h+1), reflected
    have split : Ioo 0 (2 * h + 1) = Ioc 0 h ∪ Ioo h (2 * h + 1) := by
      ext k; simp only [mem_Ioo, mem_Ioc, mem_union]; omega
    have d1 : Disjoint (Ioc 0 h) (Ioo h (2 * h + 1)) := by
      rw [disjoint_left]; intro k hk hk'; simp only [mem_Ioo, mem_Ioc] at hk hk'; omega
    rw [split, prod_union d1]
    have refl : ∏ k ∈ Ioo h (2 * h + 1), Real.tan (ang (2 * h + 1) j k) =
        ∏ k ∈ Ioc 0 h, Real.tan (ang (2 * h + 1) j (((2 * h + 1 : ℕ) : ℤ) - k)) := by
      refine prod_nbij' (fun k => 2 * h + 1 - k) (fun k => 2 * h + 1 - k) ?_ ?_ ?_ ?_ ?_
      · intro k hk; simp only [mem_coe, mem_Ioo, mem_Ioc] at hk ⊢; omega
      · intro k hk; simp only [mem_coe, mem_Ioo, mem_Ioc] at hk ⊢; omega
      · intro k hk; simp only [mem_coe, mem_Ioo] at hk; omega
      · intro k hk; simp only [mem_coe, mem_Ioc] at hk; omega
      · intro k hk
        simp only [mem_Ioo] at hk
        congr 1; push_cast [Nat.cast_sub (by omega : k ≤ 2 * h + 1)]; ring
    have he : eps (2 * h + 1) j = 1 := by unfold eps; rw [if_neg (Nat.not_even_iff_odd.mpr ⟨h, rfl⟩)]
    rw [refl, he, ← prod_mul_distrib]
    exact prod_eq_one (fun k hk => hpair k (by simp only [mem_Ioc, mem_Ioo] at hk ⊢; omega))

/-- **A full period.** The factors `-i tan x_k` for `k = 1, …, 2m - 1`, `k ≠ m`, multiply to `1`. -/
theorem period_prod (m j : ℕ) (hm : m ≠ 0) (hj : Odd j) (hc : Nat.Coprime j m) :
    (∏ k ∈ Ioo 0 m, (-Complex.I * Real.tan (ang m j k))) *
      (∏ k ∈ Ioo m (2 * m), (-Complex.I * Real.tan (ang m j k))) = 1 := by
  have refl : ∏ k ∈ Ioo m (2 * m), (-Complex.I * (Real.tan (ang m j k) : ℂ)) =
      ∏ k ∈ Ioo 0 m, (-Complex.I * (Real.tan (ang m j (((2 * m : ℕ) : ℤ) - k)) : ℂ)) := by
    refine prod_nbij' (fun k => 2 * m - k) (fun k => 2 * m - k) ?_ ?_ ?_ ?_ ?_
    · intro k hk; simp only [mem_coe, mem_Ioo] at hk ⊢; omega
    · intro k hk; simp only [mem_coe, mem_Ioo] at hk ⊢; omega
    · intro k hk; simp only [mem_coe, mem_Ioo] at hk; omega
    · intro k hk; simp only [mem_coe, mem_Ioo] at hk; omega
    · intro k hk
      simp only [mem_Ioo] at hk
      congr 3; push_cast [Nat.cast_sub (by omega : k ≤ 2 * m)]; ring
  rw [refl, ← prod_mul_distrib]
  have : ∀ k ∈ Ioo 0 m, (-Complex.I * (Real.tan (ang m j k) : ℂ)) *
      (-Complex.I * (Real.tan (ang m j (((2 * m : ℕ) : ℤ) - k)) : ℂ)) = ((Real.tan (ang m j k)) ^ 2 : ℝ) := by
    intro k _
    have hr : Real.tan (ang m j (((2 * m : ℕ) : ℤ) - k)) = -Real.tan (ang m j k) := by
      have := tan_refl m j hm k; push_cast at this ⊢; exact this
    rw [hr, Complex.ofReal_neg, Complex.ofReal_pow]
    ring_nf; rw [Complex.I_sq]; ring
  rw [prod_congr rfl this]
  have hp := prod_tan m j hm hj hc
  rw [← Complex.ofReal_prod, prod_pow, hp, sq, eps_sq m j hj, Complex.ofReal_one]

/-! ### Which tail length matters -/

/-- `A(r) = ∏_{k=1}^{r} cot x_k` (with `cot = tan⁻¹`). -/
noncomputable def A (m j r : ℕ) : ℝ := ∏ k ∈ Ioc 0 r, (Real.tan (ang m j k))⁻¹

/-- **Only `ρ' = min(ρ, m - 1 - ρ)` matters**: `A(ρ) = ε_m(j) A(m - 1 - ρ)`. -/
theorem cot_symm (m j ρ : ℕ) (hm : m ≠ 0) (hj : Odd j) (hc : Nat.Coprime j m) (hρ : ρ < m) :
    A m j ρ = eps m j * A m j (m - 1 - ρ) := by
  have hne : ∀ k ∈ Ioo 0 m, Real.tan (ang m j k) ≠ 0 := fun k hk => by
    rw [mem_Ioo] at hk; exact tan_ne_zero m j hc k hk.1 hk.2
  -- the full product of cotangents is ε⁻¹ = ε
  have full : ∏ k ∈ Ioo 0 m, (Real.tan (ang m j k))⁻¹ = eps m j := by
    rw [prod_inv_distrib, prod_tan m j hm hj hc]
    have := eps_sq m j hj
    exact inv_eq_of_mul_eq_one_right this
  have split : Ioo 0 m = Ioc 0 ρ ∪ Ioo ρ m := by ext k; simp only [mem_Ioo, mem_Ioc, mem_union]; omega
  have d : Disjoint (Ioc 0 ρ) (Ioo ρ m) := by
    rw [disjoint_left]; intro k hk hk'; simp only [mem_Ioo, mem_Ioc] at hk hk'; omega
  have tail : ∏ k ∈ Ioo ρ m, (Real.tan (ang m j k))⁻¹ = (A m j (m - 1 - ρ))⁻¹ := by
    unfold A
    rw [← prod_inv_distrib]
    simp only [inv_inv]
    refine prod_nbij' (fun k => m - k) (fun k => m - k) ?_ ?_ ?_ ?_ ?_
    · intro k hk; simp only [mem_coe, mem_Ioo, mem_Ioc] at hk ⊢; omega
    · intro k hk; simp only [mem_coe, mem_Ioo, mem_Ioc] at hk ⊢; omega
    · intro k hk; simp only [mem_coe, mem_Ioo] at hk; omega
    · intro k hk; simp only [mem_coe, mem_Ioc] at hk; omega
    · intro k hk
      simp only [mem_Ioo] at hk
      have := tan_pair m j hm hj (k : ℤ)
      rw [show ((m - k : ℕ) : ℤ) = (m : ℤ) - k by omega, this]
  have hA : A m j (m - 1 - ρ) ≠ 0 := by
    unfold A
    refine prod_ne_zero_iff.mpr fun k hk => inv_ne_zero (hne k ?_)
    simp only [mem_Ioc, mem_Ioo] at hk ⊢; omega
  rw [split, prod_union d, tail] at full
  rw [← full]
  show A m j ρ = (A m j ρ * (A m j (m - 1 - ρ))⁻¹) * A m j (m - 1 - ρ)
  rw [mul_assoc, inv_mul_cancel₀ hA, mul_one]


/-! ### Assembling the tangent product -/

/-- The factor `-i tan x_k`. -/
noncomputable def fac (m j : ℕ) (k : ℕ) : ℂ := -Complex.I * (Real.tan (ang m j k) : ℂ)

theorem fac_periodic (m j : ℕ) (hm : m ≠ 0) (k a : ℕ) : fac m j (k + 2 * m * a) = fac m j k := by
  unfold fac
  have : ang m j ((k + 2 * m * a : ℕ) : ℤ) = ang m j k + ((j * a : ℕ) : ℤ) * π := by
    unfold ang; have : (m : ℝ) ≠ 0 := by exact_mod_cast hm
    field_simp; push_cast; ring
  rw [this, tan_add_int_pi]

/-- Shifting a block by a multiple of `2m` changes nothing. -/
theorem shift (m j : ℕ) (hm : m ≠ 0) (a L : ℕ) :
    ∏ k ∈ (Ioc (2 * m * a) (2 * m * a + L)).filter (fun k => ¬ m ∣ k), fac m j k =
      ∏ k ∈ (Ioc 0 L).filter (fun k => ¬ m ∣ k), fac m j k := by
  refine prod_nbij' (fun k => k - 2 * m * a) (fun k => k + 2 * m * a) ?_ ?_ ?_ ?_ ?_
  · intro k hk
    simp only [mem_coe, mem_filter, mem_Ioc] at hk ⊢
    refine ⟨⟨by omega, by omega⟩, fun hd => hk.2 ?_⟩
    have e1 : m * (2 * a) = 2 * m * a := by ring
    have : k = (k - 2 * m * a) + m * (2 * a) := by rw [e1]; omega
    rw [this]; exact dvd_add hd (dvd_mul_right _ _)
  · intro k hk
    simp only [mem_coe, mem_filter, mem_Ioc] at hk ⊢
    refine ⟨⟨by omega, by omega⟩, fun hd => hk.2 ?_⟩
    have h2 : m ∣ 2 * m * a := ⟨2 * a, by ring⟩
    exact (Nat.dvd_add_right h2).mp (by rwa [add_comm] at hd)
  · intro k hk; simp only [mem_coe, mem_filter, mem_Ioc] at hk; omega
  · intro k hk; simp only [mem_coe, mem_filter, mem_Ioc] at hk; omega
  · intro k hk
    simp only [mem_filter, mem_Ioc] at hk
    rw [← fac_periodic m j hm (k - 2 * m * a) a, Nat.sub_add_cancel (by omega)]

/-- The non-multiples of `m` in `(0, m + r]`, `r < m`, are `(0, m)` and `(m, m + r]`. -/
theorem filter_split (m r : ℕ) (hr : r < m) :
    (Ioc 0 (m + r)).filter (fun k => ¬ m ∣ k) = Ioo 0 m ∪ Ioc m (m + r) := by
  ext k
  simp only [mem_filter, mem_Ioc, mem_Ioo, mem_union]
  constructor
  · rintro ⟨⟨h0, h1⟩, hd⟩
    by_cases hk : k = m
    · exact absurd (hk ▸ dvd_refl m) hd
    · omega
  · rintro (⟨h0, h1⟩ | ⟨h0, h1⟩)
    · exact ⟨⟨h0, by omega⟩, fun hd => absurd (Nat.le_of_dvd h0 hd) (by omega)⟩
    · refine ⟨⟨by omega, h1⟩, fun ⟨c, hc⟩ => ?_⟩
      rcases c with _ | _ | c
      · omega
      · omega
      · have : m * (c + 1 + 1) ≥ 2 * m := by nlinarith
        omega

/-- A full period of factors multiplies to `1`. -/
theorem period_filter (m j : ℕ) (hm : m ≠ 0) (hj : Odd j) (hc : Nat.Coprime j m) :
    ∏ k ∈ (Ioc 0 (2 * m)).filter (fun k => ¬ m ∣ k), fac m j k = 1 := by
  have hs : (Ioc 0 (2 * m)).filter (fun k => ¬ m ∣ k) = Ioo 0 m ∪ Ioo m (2 * m) := by
    ext k
    simp only [mem_filter, mem_Ioc, mem_Ioo, mem_union]
    constructor
    · rintro ⟨⟨h0, h1⟩, hd⟩
      rcases Nat.lt_trichotomy k m with h | h | h
      · exact Or.inl ⟨h0, h⟩
      · exact absurd (h ▸ dvd_refl m) hd
      · refine Or.inr ⟨h, lt_of_le_of_ne h1 fun he => hd ⟨2, by omega⟩⟩
    · rintro (⟨h0, h1⟩ | ⟨h0, h1⟩)
      · exact ⟨⟨h0, by omega⟩, fun hd => absurd (Nat.le_of_dvd h0 hd) (by omega)⟩
      · refine ⟨⟨by omega, h1.le⟩, fun ⟨c, hc⟩ => ?_⟩
        rcases c with _ | _ | c
        · omega
        · omega
        · have : m * (c + 1 + 1) ≥ 2 * m := by nlinarith
          omega
  have d : Disjoint (Ioo 0 m) (Ioo m (2 * m)) := by
    rw [disjoint_left]; intro k hk hk'; simp only [mem_Ioo] at hk hk'; omega
  rw [hs, prod_union d]
  exact period_prod m j hm hj hc

theorem periods (m j : ℕ) (hm : m ≠ 0) (hj : Odd j) (hc : Nat.Coprime j m) (e : ℕ) :
    ∏ k ∈ (Ioc 0 (2 * m * e)).filter (fun k => ¬ m ∣ k), fac m j k = 1 := by
  induction e with
  | zero => simp
  | succ e ih =>
    have split : Ioc 0 (2 * m * (e + 1)) = Ioc 0 (2 * m * e) ∪ Ioc (2 * m * e) (2 * m * e + 2 * m) := by
      rw [show 2 * m * (e + 1) = 2 * m * e + 2 * m by ring]
      ext k; simp only [mem_Ioc, mem_union]; omega
    have d : Disjoint (Ioc 0 (2 * m * e)) (Ioc (2 * m * e) (2 * m * e + 2 * m)) := by
      rw [disjoint_left]; intro k hk hk'; simp only [mem_Ioc] at hk hk'; omega
    rw [split, filter_union, prod_union (disjoint_filter_filter d), ih, shift m j hm e (2 * m),
      period_filter m j hm hj hc, one_mul]

/-- **The tangent product of the residue.** For `n = (2e+1) m + ρ` with `ρ < m`, the factors `-i tan x_k` over the
non-multiples `k ≤ n` of `m` multiply to `(-i)^{m-1} ε_m(j) ∏_{k ≤ ρ} i cot x_k`. -/
theorem residue_product (m j e ρ : ℕ) (hm : m ≠ 0) (hj : Odd j) (hc : Nat.Coprime j m) (hρ : ρ < m) :
    ∏ k ∈ (Ioc 0 ((2 * e + 1) * m + ρ)).filter (fun k => ¬ m ∣ k), fac m j k =
      (-Complex.I) ^ (m - 1) * (eps m j : ℂ) *
        ∏ k ∈ Ioc 0 ρ, (Complex.I * ((Real.tan (ang m j k))⁻¹ : ℝ)) := by
  have split : Ioc 0 ((2 * e + 1) * m + ρ) = Ioc 0 (2 * m * e) ∪ Ioc (2 * m * e) (2 * m * e + (m + ρ)) := by
    ext k; simp only [mem_Ioc, mem_union]
    have : (2 * e + 1) * m + ρ = 2 * m * e + (m + ρ) := by ring
    rw [this]; omega
  have d : Disjoint (Ioc 0 (2 * m * e)) (Ioc (2 * m * e) (2 * m * e + (m + ρ))) := by
    rw [disjoint_left]; intro k hk hk'; simp only [mem_Ioc] at hk hk'; omega
  rw [split, filter_union, prod_union (disjoint_filter_filter d), periods m j hm hj hc e, one_mul,
    shift m j hm e (m + ρ), filter_split m ρ hρ]
  have d2 : Disjoint (Ioo 0 m) (Ioc m (m + ρ)) := by
    rw [disjoint_left]; intro k hk hk'; simp only [mem_Ioo, mem_Ioc] at hk hk'; omega
  rw [prod_union d2]
  congr 1
  · unfold fac
    rw [prod_mul_distrib, prod_const, Nat.card_Ioo, Nat.sub_zero, ← Complex.ofReal_prod, prod_tan m j hm hj hc]
  · refine prod_nbij' (fun k => k - m) (fun k => k + m) ?_ ?_ ?_ ?_ ?_
    · intro k hk; simp only [mem_coe, mem_Ioc] at hk ⊢; omega
    · intro k hk; simp only [mem_coe, mem_Ioc] at hk ⊢; omega
    · intro k hk; simp only [mem_coe, mem_Ioc] at hk; omega
    · intro k hk; simp only [mem_coe, mem_Ioc] at hk; omega
    · intro k hk
      simp only [mem_Ioc] at hk
      unfold fac
      have := tan_tail m j hm hj ((k - m : ℕ) : ℤ)
      rw [show ((m : ℤ) + ((k - m : ℕ) : ℤ)) = ((k : ℕ) : ℤ) by omega] at this
      rw [this, Complex.ofReal_neg]
      ring

/-! ### Inversion -/

/-- `P_n(1/q) = (-1)^n P_n(q)`. -/
theorem inv_symm {K : Type*} [Field K] (q : K) (hq : q ≠ 0) (n : ℕ) :
    ∏ k ∈ Icc 1 n, (1 - q⁻¹ ^ k) / (1 + q⁻¹ ^ k) = (-1) ^ n * ∏ k ∈ Icc 1 n, (1 - q ^ k) / (1 + q ^ k) := by
  have h : ∀ k, (1 - q⁻¹ ^ k) / (1 + q⁻¹ ^ k) = -((1 - q ^ k) / (1 + q ^ k)) := by
    intro k
    have hk : q ^ k ≠ 0 := pow_ne_zero _ hq
    rw [inv_pow, show 1 - (q ^ k)⁻¹ = (q ^ k - 1) / q ^ k by field_simp,
      show 1 + (q ^ k)⁻¹ = (q ^ k + 1) / q ^ k by field_simp, div_div_div_cancel_right₀ hk, add_comm (q ^ k) 1,
      ← neg_div, neg_sub]
  rw [prod_congr rfl (fun k _ => h k), prod_neg, Nat.card_Icc, Nat.add_sub_cancel]

end TanhResidues
