import AlternatingSum.Positivity
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.SmallDegree
import Mathlib.Algebra.Polynomial.Degree.Lemmas

/-!
  Corollary 4 (Taylor's conjecture) and Taylor's degree observation: for fixed `a, b, n`,
  `ν! L(u,a,b,n) / (u+ν)!²` is a polynomial in `u` with nonnegative coefficients, and for even
  `a` with `n ≥ a/2` its degree is exactly `n - a/2`.

  The route: `[w^x z^y] R^(u+1) = C(u+h, h) C(2u+x+1+y, y)` (`x = 2h`), and both binomials are
  products of linear factors in `u` with nonnegative coefficients, divided by factorials.
-/

namespace Abdesselam

open Finset Nat

/-- `Π_{i<y} (t + i + 1) = (t+y)!/t!`. -/
theorem prod_succ_eq (t y : ℕ) : ∏ i ∈ range y, ((t : ℚ) + i + 1) = ((t + y) ! : ℚ) / (t ! : ℚ) := by
  induction y with
  | zero => rw [prod_range_zero, add_zero, div_self (by positivity)]
  | succ y ih =>
    rw [prod_range_succ, ih, ← add_assoc, Nat.factorial_succ]
    push_cast
    field_simp

/-- `C(t+y, t) = Π_{i<y} (t + i + 1) / y!`. -/
theorem choose_eq_prod (t y : ℕ) :
    ((t + y).choose t : ℚ) = (∏ i ∈ range y, ((t : ℚ) + i + 1)) / (y ! : ℚ) := by
  rw [Nat.cast_add_choose, prod_succ_eq]
  field_simp

/-- Nonnegative coefficients for polynomials. -/
def PNN (p : Polynomial ℚ) : Prop := ∀ i, 0 ≤ p.coeff i

theorem PNN_mul {p q : Polynomial ℚ} (hp : PNN p) (hq : PNN q) : PNN (p * q) := by
  intro i; rw [Polynomial.coeff_mul]; exact sum_nonneg fun x _ ↦ mul_nonneg (hp _) (hq _)

theorem PNN_C {c : ℚ} (hc : 0 ≤ c) : PNN (Polynomial.C c) := by
  intro i; rw [Polynomial.coeff_C]; split_ifs <;> simp [hc]

theorem PNN_add {p q : Polynomial ℚ} (hp : PNN p) (hq : PNN q) : PNN (p + q) := by
  intro i; rw [Polynomial.coeff_add]; exact add_nonneg (hp i) (hq i)

theorem PNN_linear {r c : ℚ} (hr : 0 ≤ r) (hc : 0 ≤ c) :
    PNN (Polynomial.C r * Polynomial.X + Polynomial.C c) := by
  refine PNN_add ?_ (PNN_C hc)
  intro i; rw [Polynomial.coeff_C_mul, Polynomial.coeff_X]; split_ifs <;> simp [hr]

theorem PNN_prod {s : Finset ℕ} {f : ℕ → Polynomial ℚ} (hf : ∀ i ∈ s, PNN (f i)) :
    PNN (∏ i ∈ s, f i) :=
  prod_induction f PNN (fun _ _ ↦ PNN_mul) (PNN_C zero_le_one |> fun h ↦ by simpa using h) hf

theorem PNN_sum {s : Finset ((Fin 2 →₀ ℕ) × (Fin 2 →₀ ℕ))} {f : _ → Polynomial ℚ}
    (hf : ∀ i ∈ s, PNN (f i)) : PNN (∑ i ∈ s, f i) :=
  sum_induction f PNN (fun _ _ ↦ PNN_add) (by simpa using PNN_C (le_refl (0 : ℚ))) hf

/-- `Π_{i<y} (r X + c + i + 1)`: evaluates to a product of linear factors. -/
noncomputable def lin (r c : ℚ) (y : ℕ) : Polynomial ℚ :=
  ∏ i ∈ range y, (Polynomial.C r * Polynomial.X + Polynomial.C (c + i + 1))

theorem PNN_lin {r c : ℚ} (hr : 0 ≤ r) (hc : 0 ≤ c) (y : ℕ) : PNN (lin r c y) :=
  PNN_prod fun i _ ↦ PNN_linear hr (by positivity)

theorem eval_lin (r c : ℚ) (y : ℕ) (u : ℚ) :
    (lin r c y).eval u = ∏ i ∈ range y, (r * u + c + i + 1) := by
  simp [lin, Polynomial.eval_prod, add_assoc]

theorem natDegree_factor (r d : ℚ) :
    (Polynomial.C r * Polynomial.X + Polynomial.C d).natDegree ≤ 1 :=
  Polynomial.natDegree_linear_le

theorem natDegree_lin (r c : ℚ) (y : ℕ) : (lin r c y).natDegree ≤ y := by
  unfold lin
  refine (Polynomial.natDegree_prod_le (range y)
    (fun i : ℕ ↦ Polynomial.C r * Polynomial.X + Polynomial.C (c + i + 1))).trans ?_
  have h := Finset.sum_le_card_nsmul (range y)
    (fun i : ℕ ↦ (Polynomial.C r * Polynomial.X + Polynomial.C (c + i + 1)).natDegree) 1
    (fun i _ ↦ natDegree_factor r (c + i + 1))
  rwa [card_range, smul_eq_mul, mul_one] at h

theorem coeff_lin_top (r c : ℚ) (y : ℕ) : (lin r c y).coeff y = r ^ y := by
  have h := Polynomial.coeff_prod_of_natDegree_le (s := range y)
    (fun i ↦ Polynomial.C r * Polynomial.X + Polynomial.C (c + i + 1)) 1
    (fun i _ ↦ natDegree_factor r (c + i + 1))
  rw [card_range, mul_one] at h
  rw [lin, h]
  simp [Polynomial.coeff_C, Polynomial.coeff_one]

/-- The polynomial in `u` contributed by the split `w^a z^b = (w^x z^y) · (rest)`. -/
noncomputable def termPoly (ν : ℕ) (p : (Fin 2 →₀ ℕ) × (Fin 2 →₀ ℕ)) : Polynomial ℚ :=
  if Even (p.1 0) then
    Polynomial.C (MvPowerSeries.coeff p.2 ((R - 1) ^ ν) / ((p.1 0 / 2) ! * (p.1 1) ! : ℚ)) *
      (lin 1 0 (p.1 0 / 2) * lin 2 (p.1 0 + 1) (p.1 1))
  else 0

theorem PNN_termPoly (ν : ℕ) (p : (Fin 2 →₀ ℕ) × (Fin 2 →₀ ℕ)) : PNN (termPoly ν p) := by
  unfold termPoly
  split_ifs
  · exact PNN_mul (PNN_C (div_nonneg (NN_pow NN_R_sub_one ν _) (by positivity)))
      (PNN_mul (PNN_lin zero_le_one le_rfl _) (PNN_lin zero_le_two (by positivity) _))
  · simpa using PNN_C (le_refl (0 : ℚ))

theorem eval_termPoly (ν u : ℕ) (p : (Fin 2 →₀ ℕ) × (Fin 2 →₀ ℕ)) :
    (termPoly ν p).eval (u : ℚ) =
      MvPowerSeries.coeff p.1 (R ^ (u + 1)) * MvPowerSeries.coeff p.2 ((R - 1) ^ ν) := by
  unfold termPoly
  rw [coeff_R_pow']
  split_ifs with hx
  · rw [Polynomial.eval_mul, Polynomial.eval_mul, Polynomial.eval_C, eval_lin, eval_lin]
    have e1 : ∏ i ∈ range (p.1 0 / 2), (1 * (u : ℚ) + 0 + i + 1) =
        ∏ i ∈ range (p.1 0 / 2), ((u : ℚ) + i + 1) := by
      refine prod_congr rfl fun i _ ↦ ?_; ring
    have e2 : ∏ i ∈ range (p.1 1), (2 * (u : ℚ) + (p.1 0 + 1 : ℕ) + i + 1) =
        ∏ i ∈ range (p.1 1), (((2 * u + p.1 0 + 1 : ℕ) : ℚ) + i + 1) := by
      refine prod_congr rfl fun i _ ↦ ?_; push_cast; ring
    rw [e1, show ((p.1 0 : ℚ) + 1) = ((p.1 0 + 1 : ℕ) : ℚ) by push_cast; ring, e2]
    have hc1 : ((u + p.1 0 / 2).choose u : ℚ) =
        (∏ i ∈ range (p.1 0 / 2), ((u : ℚ) + i + 1)) / ((p.1 0 / 2) ! : ℚ) :=
      choose_eq_prod u (p.1 0 / 2)
    have hc2 : ((2 * u + p.1 0 + 1 + p.1 1).choose (2 * u + p.1 0 + 1) : ℚ) =
        (∏ i ∈ range (p.1 1), (((2 * u + p.1 0 + 1 : ℕ) : ℚ) + i + 1)) / ((p.1 1) ! : ℚ) :=
      choose_eq_prod (2 * u + p.1 0 + 1) (p.1 1)
    rw [hc1, hc2]
    field_simp
  · simp

theorem natDegree_termPoly (ν : ℕ) (p : (Fin 2 →₀ ℕ) × (Fin 2 →₀ ℕ)) :
    (termPoly ν p).natDegree ≤ p.1 0 / 2 + p.1 1 := by
  unfold termPoly
  split_ifs
  · refine (Polynomial.natDegree_C_mul_le _ _).trans ?_
    exact Polynomial.natDegree_mul_le.trans (Nat.add_le_add (natDegree_lin _ _ _) (natDegree_lin _ _ _))
  · simp

theorem coeff_termPoly_top (ν : ℕ) (p : (Fin 2 →₀ ℕ) × (Fin 2 →₀ ℕ)) (hx : Even (p.1 0)) :
    (termPoly ν p).coeff (p.1 0 / 2 + p.1 1) =
      MvPowerSeries.coeff p.2 ((R - 1) ^ ν) / ((p.1 0 / 2) ! * (p.1 1) ! : ℚ) * 2 ^ (p.1 1) := by
  unfold termPoly
  rw [ite_eq_left hx, Polynomial.coeff_C_mul,
    Polynomial.coeff_mul_add_eq_of_natDegree_le (natDegree_lin _ _ _) (natDegree_lin _ _ _),
    coeff_lin_top, coeff_lin_top, one_pow, one_mul]

/-- **Corollary 4 (Taylor's conjecture)** with Taylor's degree observation. -/
theorem taylor (a b n : ℕ) (hn : n ≤ a + b) :
    ∃ P : Polynomial ℚ, (∀ i, 0 ≤ P.coeff i) ∧
      (∀ u : ℕ, P.eval (u : ℚ) =
        ((a + b - n) ! : ℚ) * L u a b n / ((u + (a + b - n)) ! : ℚ) ^ 2) ∧
      (Even a → a ≤ 2 * n → P.natDegree = n - a / 2) := by
  classical
  set ν := a + b - n with hν
  refine ⟨∑ p ∈ antidiagonal (mono a b), termPoly ν p,
    PNN_sum fun p _ ↦ PNN_termPoly ν p, fun u ↦ ?_, fun ha h2 ↦ ?_⟩
  · rw [Polynomial.eval_finsetSum]
    simp_rw [eval_termPoly]
    rw [← MvPowerSeries.coeff_mul, main u a b n hn, ← hν]
    field_simp
  · -- every term has degree at most `n - a/2`, by the weight bound on `(R-1)^ν`
    have hle : ∀ p ∈ antidiagonal (mono a b), ∀ i, n - a / 2 < i → (termPoly ν p).coeff i = 0 := by
      intro p hp i hi
      rw [mem_antidiagonal] at hp
      have h0 : p.1 0 + p.2 0 = a := by simpa using congrArg (· 0) hp
      have h1 : p.1 1 + p.2 1 = b := by simpa using congrArg (· 1) hp
      by_cases hc : MvPowerSeries.coeff p.2 ((R - 1) ^ ν) = 0
      · unfold termPoly; split_ifs <;> simp [hc]
      · have hw : ¬ (p.2 0 + 2 * p.2 1 < 2 * (1 * ν)) := fun h ↦ hc (Wt_pow Wt_R_sub_one ν _ h)
        refine Polynomial.coeff_eq_zero_of_natDegree_lt
          ((natDegree_termPoly ν p).trans_lt (by obtain ⟨r, hr⟩ := ha; omega))
    -- the split `w^(a-2i) z^(b-j) · w^(2i) z^j` with `i + j = ν` reaches degree `n - a/2`
    obtain ⟨r, rfl⟩ := ha
    set i := ν - min ν b with hi
    set j := min ν b with hj
    have hij : i + j = ν := by omega
    set q : (Fin 2 →₀ ℕ) × (Fin 2 →₀ ℕ) := (mono (2 * (r - i)) (b - j), mono (2 * i) j) with hq
    have hqmem : q ∈ antidiagonal (mono (r + r) b) := by
      rw [mem_antidiagonal, hq, mono_add]; congr 1 <;> omega
    have hpos : 0 < (termPoly ν q).coeff (n - (r + r) / 2) := by
      have hdeg : n - (r + r) / 2 = q.1 0 / 2 + q.1 1 := by simp [hq]; omega
      rw [hdeg, coeff_termPoly_top ν q (by simp [hq])]
      have := pos_R_sub_one_pow i j
      rw [hij] at this
      simp only [hq] at this ⊢
      positivity
    have htop : 0 < (∑ p ∈ antidiagonal (mono (r + r) b), termPoly ν p).coeff (n - (r + r) / 2) := by
      rw [Polynomial.finsetSum_coeff]
      exact lt_of_lt_of_le hpos (single_le_sum (f := fun p ↦ (termPoly ν p).coeff (n - (r + r) / 2))
        (fun p _ ↦ PNN_termPoly ν p _) hqmem)
    refine le_antisymm ?_ (Polynomial.le_natDegree_of_ne_zero htop.ne')
    rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro k hk
    rw [Polynomial.finsetSum_coeff]
    exact sum_eq_zero fun p hp ↦ hle p hp k (by exact_mod_cast hk)

end Abdesselam
