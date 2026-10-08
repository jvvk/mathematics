/-
  Stanley, MathOverflow 486548. Theorem 2: doubly alternating permutations.
  The Euler-number series is proved in EulerSeries.lean, from the Entringer triangle and
  Mathlib's Bernoulli-polynomial Fourier expansions. These generic asymptotic lemmas take
  StanleyGF as a parameter; StanleyProof.lean proves that enumerative identity and supplies
  the unconditional headline theorems g_asymptotics and g_asymptotics'.
-/
import LeanProofs.Stanley.EulerSeries

namespace Stanley

namespace Alt

open Finset PowerSeries
open scoped Nat

/-! ### Even power series -/

/-- `P(x) ↦ P(x²)`. -/
noncomputable def ev (P : PowerSeries ℝ) : PowerSeries ℝ :=
  mk fun i => if Even i then coeff (i / 2) P else 0

theorem coeff_ev (P : PowerSeries ℝ) (i : ℕ) :
    coeff i (ev P) = if Even i then coeff (i / 2) P else 0 := by simp [ev]

theorem ev_mul (P Q : PowerSeries ℝ) : ev (P * Q) = ev P * ev Q := by
  ext i
  rw [coeff_ev, coeff_mul, coeff_mul]
  simp only [coeff_ev]
  by_cases hi : Even i
  · rw [if_pos hi]
    obtain ⟨t, rfl⟩ := hi
    have ht : (t + t) / 2 = t := by omega
    rw [ht]
    symm
    rw [← Finset.sum_filter_of_ne (p := fun q : ℕ × ℕ => Even q.1 ∧ Even q.2)]
    · apply Finset.sum_nbij' (fun q => (q.1 / 2, q.2 / 2)) (fun q => (2 * q.1, 2 * q.2))
      · intro q hq
        simp only [Finset.mem_filter, Finset.mem_antidiagonal] at hq ⊢
        obtain ⟨h, ⟨a, ha⟩, ⟨b, hb⟩⟩ := hq
        omega
      · intro q hq
        simp only [Finset.mem_filter, Finset.mem_antidiagonal, Finset.mem_coe] at hq ⊢
        refine ⟨by omega, ⟨q.1, by ring⟩, ⟨q.2, by ring⟩⟩
      · intro q hq
        simp only [Finset.mem_filter, Finset.mem_antidiagonal, Finset.mem_coe] at hq
        obtain ⟨_, ⟨a, ha⟩, ⟨b, hb⟩⟩ := hq
        ext <;> simp <;> omega
      · intro q _; ext <;> simp
      · intro q hq
        simp only [Finset.mem_filter, Finset.mem_antidiagonal, Finset.mem_coe] at hq
        rw [if_pos hq.2.1, if_pos hq.2.2]
    · intro q _ hq
      by_contra hc
      apply hq
      by_cases h1 : Even q.1 <;> by_cases h2 : Even q.2 <;> simp_all
  · rw [if_neg hi]
    symm
    apply Finset.sum_eq_zero
    intro q hq
    rw [Finset.mem_antidiagonal] at hq
    by_cases h1 : Even q.1
    · have h2 : ¬ Even q.2 := fun h2 => hi (hq ▸ h1.add h2)
      rw [if_neg h2, mul_zero]
    · rw [if_neg h1, zero_mul]

theorem ev_one : ev 1 = 1 := by
  ext i; rw [coeff_ev, coeff_one, coeff_one]
  by_cases h : i = 0
  · subst h; simp
  · have : i / 2 = 0 → ¬ Even i := fun h0 he => by obtain ⟨t, rfl⟩ := he; omega
    split_ifs <;> simp_all

theorem ev_pow (P : PowerSeries ℝ) (m : ℕ) : ev (P ^ m) = ev P ^ m := by
  induction m with
  | zero => simp [ev_one]
  | succ m ih => rw [pow_succ, ev_mul, ih, pow_succ]

/-- `artanh x / x` in the variable `y = x²`. -/
noncomputable def V : PowerSeries ℝ := mk fun t => (1 : ℝ) / (2 * t + 1)

/-- `(1 - y)^(-1/2)`. -/
noncomputable def S : PowerSeries ℝ := mk fun t => (((2 * t).choose t : ℕ) : ℝ) / 4 ^ t

theorem u_eq : u = X * ev V := by
  ext i
  rcases i with _ | i
  · simp [u]
  · rw [coeff_succ_X_mul, coeff_ev]
    simp only [u, V, coeff_mk]
    by_cases h : Even i
    · obtain ⟨t, rfl⟩ := h
      have h1 : Odd (t + t + 1) := ⟨t, by ring⟩
      rw [if_pos h1, if_pos ⟨t, rfl⟩, show (t + t) / 2 = t by omega]
      push_cast; ring_nf
    · have h1 : ¬ Odd (i + 1) := by
        rw [Nat.not_odd_iff_even]; exact (Nat.not_even_iff_odd.mp h).add_one
      rw [if_neg h1, if_neg h]

theorem s_eq : s = ev S := by
  ext i
  rw [coeff_ev]
  simp only [s, S, coeff_mk]
  by_cases h : Even i
  · obtain ⟨t, rfl⟩ := h
    rw [if_pos ⟨t, rfl⟩, if_pos ⟨t, rfl⟩, show (t + t) / 2 = t by omega, show t + t = 2 * t by ring]
  · rw [if_neg h, if_neg h]

/-- The series whose coefficient `(n-m)/2` is `c_{n,m}`. -/
noncomputable def Y (m : ℕ) : PowerSeries ℝ := if Odd m then V ^ m else S * V ^ m

theorem cc_eq (n m : ℕ) :
    cc n m = if m ≤ n ∧ Even (n - m) then coeff ((n - m) / 2) (Y m) else 0 := by
  have key : (if Odd m then u ^ m else s * u ^ m) = X ^ m * ev (Y m) := by
    unfold Y
    rw [u_eq, s_eq, mul_pow]
    split_ifs
    · rw [ev_pow]
    · rw [ev_mul, ev_pow]; ring
  unfold cc
  rw [key, coeff_X_pow_mul', coeff_ev]
  split_ifs <;> simp_all

/-! ### Coefficient domination -/

/-- `0 ≤ f ≤ F` coefficientwise. -/
def Dom (f F : PowerSeries ℝ) : Prop := ∀ i, 0 ≤ coeff i f ∧ coeff i f ≤ coeff i F

theorem Dom.mul {f F h H : PowerSeries ℝ} (hf : Dom f F) (hh : Dom h H) : Dom (f * h) (F * H) := by
  intro i
  rw [coeff_mul, coeff_mul]
  refine ⟨Finset.sum_nonneg fun p _ => mul_nonneg (hf _).1 (hh _).1,
    Finset.sum_le_sum fun p _ => mul_le_mul (hf _).2 (hh _).2 (hh _).1 ((hf _).1.trans (hf _).2)⟩

theorem dom_one : Dom 1 1 := fun i => by rw [coeff_one]; split_ifs <;> norm_num

theorem Dom.pow {f F : PowerSeries ℝ} (hf : Dom f F) (m : ℕ) : Dom (f ^ m) (F ^ m) := by
  induction m with
  | zero => simpa using dom_one
  | succ m ih => rw [pow_succ, pow_succ]; exact ih.mul hf

/-- `1/(1 - y)`. -/
noncomputable def W : PowerSeries ℝ := mk 1

theorem dom_V : Dom V W := fun t => by
  simp only [V, W, coeff_mk, Pi.one_apply]
  constructor
  · positivity
  · rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg t : (0 : ℝ) ≤ t)]

theorem dom_S : Dom S W := fun t => by
  simp only [S, W, coeff_mk, Pi.one_apply]
  constructor
  · positivity
  · rw [div_le_one (by positivity)]
    have := Nat.centralBinom_le_four_pow t
    rw [Nat.centralBinom_eq_two_mul_choose] at this
    exact_mod_cast this

theorem dom_one_W : Dom 1 W := fun i => by
  simp only [W, coeff_one, coeff_mk, Pi.one_apply]; split_ifs <;> norm_num

theorem coeff_W_pow (m j : ℕ) : coeff j (W ^ (m + 1)) = ((m + j).choose m : ℝ) := by
  unfold W; rw [mk_one_pow_eq_mk_choose_add, coeff_mk]

/-- `c_{n,m} ≤ C(m + j, j)` for `n = m + 2j` (paper: `[xⁿ] xᵐ (1-x²)^(-m-1)`). -/
theorem dom_Y (m : ℕ) (j : ℕ) : 0 ≤ coeff j (Y m) ∧ coeff j (Y m) ≤ ((m + j).choose m : ℝ) := by
  rw [← coeff_W_pow]
  unfold Y
  split_ifs
  · have := (dom_V.pow m).mul dom_one_W j
    rwa [mul_one, ← pow_succ] at this
  · have := dom_S.mul (dom_V.pow m) j
    rwa [← pow_succ'] at this

theorem cc_nonneg (n m : ℕ) : 0 ≤ cc n m := by
  rw [cc_eq]; split_ifs
  · exact (dom_Y m _).1
  · exact le_rfl

/-! ### The two leading coefficients -/

theorem coeff_one_mul' (f h : PowerSeries ℝ) :
    coeff 1 (f * h) = coeff 0 f * coeff 1 h + coeff 1 f * coeff 0 h := by
  rw [coeff_mul, Finset.Nat.antidiagonal_succ]
  simp

theorem coeff_zero_mul' (f h : PowerSeries ℝ) : coeff 0 (f * h) = coeff 0 f * coeff 0 h := by
  rw [coeff_mul]; simp

theorem V_pow_coeff (m : ℕ) : coeff 0 (V ^ m) = 1 ∧ coeff 1 (V ^ m) = (m : ℝ) / 3 := by
  induction m with
  | zero => simp [coeff_one]
  | succ m ih =>
    rw [pow_succ, coeff_zero_mul', coeff_one_mul', ih.1, ih.2]
    simp only [V, coeff_mk]
    push_cast; constructor <;> ring

theorem Y_coeff (m : ℕ) :
    coeff 0 (Y m) = 1 ∧ coeff 1 (Y m) = (m : ℝ) / 3 + if Odd m then 0 else 1 / 2 := by
  obtain ⟨h0, h1⟩ := V_pow_coeff m
  unfold Y
  split_ifs
  · exact ⟨h0, by rw [h1]; ring⟩
  · rw [coeff_zero_mul', coeff_one_mul', h0, h1]
    simp only [S, coeff_mk]
    norm_num

theorem cc_self (n : ℕ) : cc n n = 1 := by
  rw [cc_eq, if_pos ⟨le_rfl, by simp⟩, Nat.sub_self, Nat.zero_div]; exact (Y_coeff n).1

theorem cc_two (m : ℕ) : cc (m + 2) m = (m : ℝ) / 3 + if Odd m then 0 else 1 / 2 := by
  rw [cc_eq, if_pos ⟨by omega, ⟨1, by omega⟩⟩, show (m + 2 - m) / 2 = 1 by omega]
  exact (Y_coeff m).2

theorem cc_odd {n m : ℕ} (h : ¬ Even (n - m)) : cc n m = 0 := by
  rw [cc_eq, if_neg (fun hc => h hc.2)]

theorem cc_le {n m j : ℕ} (h : n = m + 2 * j) : cc n m ≤ ((m + j).choose m : ℝ) := by
  rw [cc_eq, if_pos ⟨by omega, ⟨j, by omega⟩⟩, show (n - m) / 2 = j by omega]
  exact (dom_Y m j).2

/-! ### The series `σ_m` -/

theorem hasSum_inv_sq_succ :
    HasSum (fun k : ℕ => (1 : ℝ) / ((k : ℝ) + 1) ^ 2) (Real.pi ^ 2 / 6) := by
  have h := (hasSum_nat_add_iff' 1).mpr hasSum_zeta_two
  simp only [Finset.range_one, Finset.sum_singleton, Nat.cast_zero, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, zero_pow, div_zero, sub_zero, Nat.cast_add, Nat.cast_one] at h
  exact h

theorem pi_sq_lt : Real.pi ^ 2 < 10 := by
  have := Real.pi_lt_d2; have := Real.pi_pos; nlinarith

theorem pi_sq_gt : 9 < Real.pi ^ 2 := by
  have := Real.pi_gt_three; nlinarith

/-- `|σ_m - 1| ≤ (3/2)/3^m` for `m ≥ 1`. -/
theorem σ_close {m : ℕ} (hm : 1 ≤ m) : |σ m - 1| ≤ 3 / 2 / 3 ^ m := by
  set t : ℕ → ℝ := fun k => (-1 : ℝ) ^ (k * (m + 1)) / (2 * k + 1 : ℝ) ^ (m + 1)
  have habs : ∀ k, |t k| = 1 / (2 * k + 1 : ℝ) ^ (m + 1) := fun k => by
    simp only [t, abs_div, abs_pow, abs_neg, abs_one, one_pow]
    rw [abs_of_pos (by positivity)]
  -- domination by `c / (k+1)^2`
  set c : ℝ := 1 / 3 ^ (m - 1) * (1 / 4)
  have hc : 0 ≤ c := by positivity
  have hdom : ∀ k, |t (k + 1)| ≤ c * (1 / ((k : ℝ) + 1) ^ 2) := by
    intro k
    rw [habs]
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have h1 : (3 : ℝ) ^ (m - 1) * (4 * ((k : ℝ) + 1) ^ 2) ≤ (2 * ((k + 1 : ℕ) : ℝ) + 1) ^ (m + 1) := by
      have hsplit : (2 * ((k + 1 : ℕ) : ℝ) + 1) ^ (m + 1) =
          (2 * ((k + 1 : ℕ) : ℝ) + 1) ^ (m - 1) * (2 * ((k + 1 : ℕ) : ℝ) + 1) ^ 2 := by
        rw [← pow_add]; congr 1; omega
      rw [hsplit]
      push_cast
      apply mul_le_mul _ (by nlinarith) (by positivity) (by positivity)
      exact pow_le_pow_left₀ (by norm_num) (by linarith) _
    simp only [c]
    rw [div_mul_div_comm, div_mul_div_comm, one_mul, one_mul,
      div_le_div_iff₀ (by positivity) (by positivity), one_mul]
    nlinarith [h1]
  have hsumg : Summable (fun k : ℕ => c * (1 / ((k : ℝ) + 1) ^ 2)) :=
    (hasSum_inv_sq_succ.mul_left c).summable
  have hsum1 : Summable (fun k => t (k + 1)) :=
    Summable.of_norm_bounded hsumg (fun k => by rw [Real.norm_eq_abs]; exact hdom k)
  have hsum : Summable t := (summable_nat_add_iff 1).mp hsum1
  have h0 : t 0 = 1 := by simp [t]
  have hσ : σ m = 1 + ∑' k, t (k + 1) := by
    show ∑' k, t k = _
    rw [hsum.tsum_eq_zero_add, h0]
  rw [hσ, add_sub_cancel_left]
  calc |∑' k, t (k + 1)| ≤ ∑' k, |t (k + 1)| := by
        have := norm_tsum_le_tsum_norm (f := fun k => t (k + 1))
          (hsum1.norm)
        simpa [Real.norm_eq_abs] using this
    _ ≤ ∑' k : ℕ, c * (1 / ((k : ℝ) + 1) ^ 2) :=
        Summable.tsum_le_tsum hdom hsum1.abs hsumg
    _ = c * (Real.pi ^ 2 / 6) := (hasSum_inv_sq_succ.mul_left c).tsum_eq
    _ ≤ 3 / 2 / 3 ^ m := by
        simp only [c]
        have h3 : (3 : ℝ) ^ m = 3 ^ (m - 1) * 3 := by rw [← pow_succ]; congr 1; omega
        rw [h3]
        have := pi_sq_lt
        have hp : (0 : ℝ) < 3 ^ (m - 1) := by positivity
        rw [div_mul_div_comm, one_mul, div_mul_div_comm, div_le_div_iff₀ (by positivity)
          (by positivity)]
        nlinarith

theorem σ_bounds {m : ℕ} (hm : 1 ≤ m) : 1 / 2 ≤ σ m ∧ σ m ≤ 3 / 2 := by
  have h := σ_close hm
  have h3 : (3 : ℝ) ≤ 3 ^ m := by
    calc (3 : ℝ) = 3 ^ 1 := by norm_num
      _ ≤ 3 ^ m := pow_le_pow_right₀ (by norm_num) hm
  have : 3 / 2 / (3 : ℝ) ^ m ≤ 1 / 2 := by
    rw [div_le_iff₀ (by positivity)]; nlinarith
  constructor <;> linarith [abs_le.mp h]

/-! ### The ratios `a_m / a_n` -/

/-- `r = π²/4 = 1/ρ`. -/
noncomputable def r : ℝ := Real.pi ^ 2 / 4

theorem r_bounds : 2 < r ∧ r < 3 := by
  unfold r; constructor <;> linarith [pi_sq_lt, pi_sq_gt]

theorem r_pos : 0 < r := by linarith [r_bounds.1]

theorem a_zero : a 0 = 1 := by
  simp [a, show E 0 = 1 by decide]

/-- `a_m = 4 m! σ_m² / r^(m+1)` for `m ≥ 1`. -/
theorem a_formula {m : ℕ} (hm : 1 ≤ m) :
    a m = 4 * m ! * σ m ^ 2 / r ^ (m + 1) := by
  have hf : (0 : ℝ) < m ! := by exact_mod_cast Nat.factorial_pos m
  have hE : (E m : ℝ) = m ! * (2 * (2 / Real.pi) ^ (m + 1) * σ m) := by
    rw [← eulerSeries m hm]; field_simp
  have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
  have hr : (2 / Real.pi) ^ (2 * (m + 1)) = 1 / r ^ (m + 1) := by
    rw [pow_mul, one_div, ← inv_pow]; congr 1; unfold r; field_simp; ring
  unfold a
  rw [hE]
  have : (m ! * (2 * (2 / Real.pi) ^ (m + 1) * σ m)) ^ 2 / m ! =
      4 * m ! * σ m ^ 2 * (2 / Real.pi) ^ (2 * (m + 1)) := by
    rw [pow_mul']; field_simp; ring
  rw [this, hr]; ring

theorem a_pos (m : ℕ) : 0 < a m := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · rw [a_zero]; norm_num
  · rw [a_formula hm]
    have := (σ_bounds hm).1
    have := r_pos
    positivity

/-- `a_m / a_{m+d} ≤ 9 r^d m!/(m+d)!`. -/
theorem ratio_le (m d : ℕ) (hn : 1 ≤ m + d) :
    a m / a (m + d) ≤ 9 * r ^ d * m ! / (m + d) ! := by
  have hr := r_pos
  have hr3 := r_bounds.2
  have hfn : (0 : ℝ) < (m + d) ! := by exact_mod_cast Nat.factorial_pos _
  have hfm : (0 : ℝ) < m ! := by exact_mod_cast Nat.factorial_pos _
  obtain ⟨hσn1, hσn2⟩ := σ_bounds hn
  rw [a_formula hn, div_le_iff₀ (by positivity)]
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · rw [a_zero]
    simp only [zero_add, Nat.factorial_zero, Nat.cast_one, mul_one] at *
    have h36 : r ≤ 36 * σ d ^ 2 := by nlinarith
    have hrd := pow_pos hr d
    rw [pow_succ]
    field_simp
    nlinarith [mul_le_mul_of_nonneg_left h36 hrd.le, pow_succ r d]
  · obtain ⟨hσm1, hσm2⟩ := σ_bounds hm
    rw [a_formula hm]
    have hrm : 0 < r ^ (m + 1) := pow_pos hr _
    have hrd : 0 < r ^ d := pow_pos hr _
    have hR : 9 * r ^ d * m ! / (m + d) ! * (4 * (m + d) ! * σ (m + d) ^ 2 / r ^ (m + d + 1)) =
        36 * m ! * σ (m + d) ^ 2 / r ^ (m + 1) := by
      rw [show m + d + 1 = (m + 1) + d by ring, pow_add]; field_simp; ring
    rw [hR]
    apply div_le_div_of_nonneg_right _ hrm.le
    have : σ m ^ 2 ≤ 9 * σ (m + d) ^ 2 := by nlinarith
    nlinarith

/-- The exact ratio used for the main term. -/
theorem ratio_two {m : ℕ} (hm : 1 ≤ m) :
    a m / a (m + 2) = r ^ 2 / ((m + 1 : ℝ) * (m + 2)) * (σ m / σ (m + 2)) ^ 2 := by
  have hr := r_pos
  have h1 := (σ_bounds hm).1
  have h3 := (σ_bounds (show 1 ≤ m + 2 by omega)).1
  rw [a_formula hm, a_formula (by omega), Nat.factorial_succ, Nat.factorial_succ]
  push_cast
  have hfm : (0 : ℝ) < m ! := by exact_mod_cast Nat.factorial_pos m
  rw [show m + 2 + 1 = (m + 1) + 2 by ring, pow_add]
  field_simp
  ring

/-! ### The tail `j ≥ 2` -/

theorem tail_term {m j : ℕ} (hj : 2 ≤ j) :
    a m / a (m + 2 * j) * cc (m + 2 * j) m ≤
      9 * (2 * r ^ 2 / ((m + 2 * j : ℕ) : ℝ)) ^ 2 *
        ((2 * r ^ 2 / ((m + 2 * j : ℕ) : ℝ)) ^ (j - 2) / (j - 2) !) := by
  set n := m + 2 * j with hn
  have hn1 : 1 ≤ n := by omega
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
  set x := 2 * r ^ 2 / (n : ℝ) with hx
  have hxpos : 0 ≤ x := by have := r_pos; positivity
  have hr := ratio_le m (2 * j) hn1
  have hcc := cc_le (n := n) (m := m) (j := j) rfl
  have hc0 := cc_nonneg n m
  have hfj : (0 : ℝ) < j ! := by exact_mod_cast Nat.factorial_pos j
  have hfn : (0 : ℝ) < n ! := by exact_mod_cast Nat.factorial_pos n
  -- `m! C(m+j, m) = (m+j)!/j!` and `(m+j)! (m+j+1)^j ≤ n!`
  have hchoose : (m ! : ℝ) * ((m + j).choose m : ℝ) * j ! = (m + j) ! := by
    have := Nat.choose_mul_factorial_mul_factorial (show m ≤ m + j by omega)
    rw [show m + j - m = j by omega] at this
    exact_mod_cast (by rw [← this]; ring)
  have hfac : ((m + j) ! : ℝ) * ((m + j + 1 : ℕ) : ℝ) ^ j ≤ n ! := by
    have := Nat.factorial_mul_pow_le_factorial (m := m + j) (n := j)
    rw [show m + j + j = n by omega] at this
    exact_mod_cast this
  have hhalf : (n : ℝ) / 2 ≤ ((m + j + 1 : ℕ) : ℝ) := by
    push_cast; rw [hn]; push_cast; linarith
  -- assemble: term ≤ 9 r^(2j) (m+j)!/(j! n!) ≤ 9 x^j / j!
  have step1 : a m / a n * cc n m ≤ 9 * r ^ (2 * j) * (m + j) ! / (j ! * n !) := by
    calc a m / a n * cc n m ≤ 9 * r ^ (2 * j) * m ! / n ! * ((m + j).choose m : ℝ) :=
          mul_le_mul hr hcc hc0 (by have := r_pos; positivity)
      _ = 9 * r ^ (2 * j) * (m + j) ! / (j ! * n !) := by
          rw [← hchoose]; field_simp
  have step2 : ((m + j) ! : ℝ) / n ! ≤ (2 / n) ^ j := by
    have hq : (0 : ℝ) < ((m + j + 1 : ℕ) : ℝ) := by positivity
    rw [div_le_iff₀ hfn]
    calc ((m + j) ! : ℝ) = (m + j) ! * ((m + j + 1 : ℕ) : ℝ) ^ j / ((m + j + 1 : ℕ) : ℝ) ^ j := by
          field_simp
      _ ≤ n ! / ((m + j + 1 : ℕ) : ℝ) ^ j := by gcongr
      _ ≤ n ! / ((n : ℝ) / 2) ^ j := by gcongr
      _ = (2 / n) ^ j * n ! := by rw [div_pow, div_pow]; field_simp
  have step3 : 9 * r ^ (2 * j) * (m + j) ! / (j ! * n !) ≤ 9 * x ^ j / j ! := by
    have : 9 * r ^ (2 * j) * (m + j) ! / (j ! * n !) =
        9 * r ^ (2 * j) / j ! * (((m + j) ! : ℝ) / n !) := by field_simp
    rw [this, hx, div_pow, show r ^ (2 * j) = (r ^ 2) ^ j by rw [pow_mul]]
    calc 9 * (r ^ 2) ^ j / j ! * (((m + j) ! : ℝ) / n !) ≤ 9 * (r ^ 2) ^ j / j ! * (2 / n) ^ j :=
          mul_le_mul_of_nonneg_left step2 (by have := r_pos; positivity)
      _ = 9 * (2 * r ^ 2) ^ j / (n : ℝ) ^ j / j ! := by
          rw [div_pow, mul_pow]; field_simp
      _ = 9 * ((2 * r ^ 2) ^ j / (n : ℝ) ^ j) / j ! := by ring
  have step4 : 9 * x ^ j / j ! ≤ 9 * x ^ 2 * (x ^ (j - 2) / (j - 2) !) := by
    have hj2 : x ^ j = x ^ 2 * x ^ (j - 2) := by rw [← pow_add]; congr 1; omega
    have hf2 : ((j - 2) ! : ℝ) ≤ j ! := by exact_mod_cast Nat.factorial_le (by omega)
    have hf2p : (0 : ℝ) < (j - 2) ! := by exact_mod_cast Nat.factorial_pos _
    have hle : x ^ (j - 2) / j ! ≤ x ^ (j - 2) / (j - 2) ! :=
      div_le_div_of_nonneg_left (pow_nonneg hxpos _) hf2p hf2
    rw [hj2, show 9 * (x ^ 2 * x ^ (j - 2)) / (j ! : ℝ) = 9 * x ^ 2 * (x ^ (j - 2) / j !) by ring]
    exact mul_le_mul_of_nonneg_left hle (by positivity)
  exact step1.trans (step3.trans step4)

/-! ### Summing the tail -/

theorem tail_sum (k : ℕ) :
    ∑ m ∈ range (k + 1), a m / a (k + 3) * cc (k + 3) m ≤
      9 * (2 * r ^ 2 / ((k + 3 : ℕ) : ℝ)) ^ 2 * Real.exp (2 * r ^ 2 / ((k + 3 : ℕ) : ℝ)) := by
  set n := k + 3
  set x := 2 * r ^ 2 / (n : ℝ) with hx
  have hxpos : 0 ≤ x := by have := r_pos; positivity
  set F : ℕ → ℝ := fun i => x ^ i / (i ! : ℝ)
  have hF : ∀ i, 0 ≤ F i := fun i => by positivity
  set ψ : ℕ → ℕ := fun m => (n - m) / 2 - 2
  set P := (range (k + 1)).filter (fun m => Even (n - m))
  have hterm : ∀ m ∈ range (k + 1), a m / a n * cc n m ≤
      if Even (n - m) then 9 * x ^ 2 * F (ψ m) else 0 := by
    intro m hm
    have hmk := Finset.mem_range.mp hm
    split_ifs with he
    · obtain ⟨j, hj⟩ := he
      have hnj : n = m + 2 * j := by omega
      have hψ : ψ m = j - 2 := by simp only [ψ]; omega
      have := tail_term (m := m) (j := j) (by omega)
      rw [← hnj] at this
      rw [hψ]; exact this
    · rw [cc_odd he, mul_zero]
  calc ∑ m ∈ range (k + 1), a m / a n * cc n m
      ≤ ∑ m ∈ range (k + 1), (if Even (n - m) then 9 * x ^ 2 * F (ψ m) else 0) :=
        Finset.sum_le_sum hterm
    _ = 9 * x ^ 2 * ∑ m ∈ P, F (ψ m) := by rw [← Finset.sum_filter, Finset.mul_sum]
    _ = 9 * x ^ 2 * ∑ i ∈ P.image ψ, F i := by
        congr 1
        rw [Finset.sum_image]
        intro m hm m' hm' h
        simp only [P, Finset.coe_filter, Finset.mem_range, Set.mem_setOf_eq] at hm hm'
        obtain ⟨⟨_, ⟨j, hj⟩⟩, ⟨_, ⟨j', hj'⟩⟩⟩ := And.intro hm hm'
        simp only [ψ] at h
        omega
    _ ≤ 9 * x ^ 2 * ∑ i ∈ range n, F i := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro i hi
          obtain ⟨m, _, rfl⟩ := Finset.mem_image.mp hi
          simp only [ψ, Finset.mem_range]; omega
        · intro i _ _; exact hF i
    _ ≤ 9 * x ^ 2 * Real.exp x := by gcongr; exact Real.sum_le_exp_of_nonneg hxpos n

/-! ### The main term `j = 1` -/

theorem three_pow_ge (n : ℕ) : (n : ℝ) ^ 2 ≤ 3 ^ n := by
  have : n ^ 2 ≤ 3 ^ n := by
    induction n with
    | zero => norm_num
    | succ n ih =>
      have h3 : n < 3 ^ n := Nat.lt_pow_self (by norm_num)
      rw [pow_succ 3 n]; nlinarith
  exact_mod_cast this

/-- The arithmetic of the main term, with the series values abstracted. -/
theorem main_alg {r p q ε c n : ℝ} (hr : 0 < r) (hp1 : 1 / 2 ≤ p) (hp2 : p ≤ 3 / 2)
    (hq1 : 1 / 2 ≤ q) (hq2 : q ≤ 3 / 2) (hpε : |p - 1| ≤ 27 / 2 * ε) (hqε : |q - 1| ≤ 3 / 2 * ε)
    (hεn : ε * n ≤ 1) (hn3 : 3 ≤ n) (hc0 : 0 ≤ c) (hcn : c ≤ n) (hcoff : |c - (n - 1) / 3| ≤ 1 / 3) :
    |r ^ 2 / ((n - 1) * n) * (p / q) ^ 2 * c - r ^ 2 / (3 * n)| ≤ 362 * r ^ 2 / n ^ 2 := by
  have hq0 : 0 < q := by linarith
  have hε0 : 0 ≤ ε := by
    have := abs_nonneg (q - 1); linarith
  have hpq : |p - q| ≤ 15 * ε := by
    have := abs_sub_le p 1 q
    rw [abs_sub_comm 1 q] at this; linarith
  have hsum : |p + q| ≤ 3 := by rw [abs_of_pos (by linarith)]; linarith
  have hsq : |p ^ 2 - q ^ 2| ≤ 45 * ε := by
    rw [show p ^ 2 - q ^ 2 = (p - q) * (p + q) by ring, abs_mul]
    calc |p - q| * |p + q| ≤ (15 * ε) * 3 :=
          mul_le_mul hpq hsum (abs_nonneg _) (by positivity)
      _ = 45 * ε := by ring
  have hQ : |(p / q) ^ 2 - 1| ≤ 180 * ε := by
    have hq2p : 0 < q ^ 2 := pow_pos hq0 2
    rw [div_pow, div_sub_one hq2p.ne', abs_div, abs_of_pos hq2p, div_le_iff₀ hq2p]
    have h4 : (1 : ℝ) / 4 ≤ q ^ 2 := by nlinarith
    have := mul_le_mul_of_nonneg_left h4 (by positivity : (0 : ℝ) ≤ 180 * ε)
    linarith
  have hB : |(p / q) ^ 2 * c - (n - 1) / 3| ≤ 181 := by
    have he : (p / q) ^ 2 * c - (n - 1) / 3 = ((p / q) ^ 2 - 1) * c + (c - (n - 1) / 3) := by ring
    rw [he]
    have h1 : |((p / q) ^ 2 - 1) * c| ≤ 180 * ε * n := by
      rw [abs_mul, abs_of_nonneg hc0]
      exact mul_le_mul hQ hcn hc0 (by positivity)
    calc |((p / q) ^ 2 - 1) * c + (c - (n - 1) / 3)|
        ≤ |((p / q) ^ 2 - 1) * c| + |c - (n - 1) / 3| := abs_add_le _ _
      _ ≤ 180 * ε * n + 1 / 3 := add_le_add h1 hcoff
      _ ≤ 181 := by nlinarith
  have hden : 0 < (n - 1) * n := by nlinarith
  have hn0 : n ≠ 0 := by linarith
  have hn1 : n - 1 ≠ 0 := by linarith
  have hexpr : r ^ 2 / ((n - 1) * n) * (p / q) ^ 2 * c - r ^ 2 / (3 * n) =
      r ^ 2 * ((p / q) ^ 2 * c - (n - 1) / 3) / ((n - 1) * n) := by
    field_simp
  rw [hexpr, abs_div, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < r ^ 2),
    abs_of_pos hden, div_le_div_iff₀ hden (by positivity)]
  have h181 : r ^ 2 * |(p / q) ^ 2 * c - (n - 1) / 3| ≤ r ^ 2 * 181 :=
    mul_le_mul_of_nonneg_left hB (by positivity)
  have hn2 : n ^ 2 ≤ 2 * ((n - 1) * n) := by nlinarith
  calc r ^ 2 * |(p / q) ^ 2 * c - (n - 1) / 3| * n ^ 2 ≤ r ^ 2 * 181 * n ^ 2 :=
        mul_le_mul_of_nonneg_right h181 (by positivity)
    _ ≤ r ^ 2 * 181 * (2 * ((n - 1) * n)) :=
        mul_le_mul_of_nonneg_left hn2 (by positivity)
    _ = 362 * r ^ 2 * ((n - 1) * n) := by ring

theorem main_term (k : ℕ) :
    |a (k + 1) / a (k + 3) * cc (k + 3) (k + 1) - r ^ 2 / (3 * ((k + 3 : ℕ) : ℝ))| ≤
      362 * r ^ 2 / ((k + 3 : ℕ) : ℝ) ^ 2 := by
  have hrat := ratio_two (m := k + 1) (by omega)
  have hc := cc_two (k + 1)
  rw [show k + 1 + 2 = k + 3 by ring] at hrat hc
  rw [hrat, hc]
  obtain ⟨hp1, hp2⟩ := σ_bounds (m := k + 1) (by omega)
  obtain ⟨hq1, hq2⟩ := σ_bounds (m := k + 3) (by omega)
  have e9 : (3 : ℝ) ^ (k + 3) = 3 ^ (k + 1) * 9 := by
    rw [show k + 3 = (k + 1) + 2 by ring, pow_add]; norm_num
  have hpε : |σ (k + 1) - 1| ≤ 27 / 2 * (1 / 3 ^ (k + 3)) :=
    (σ_close (m := k + 1) (by omega)).trans (le_of_eq (by rw [e9]; field_simp; ring))
  have hqε : |σ (k + 3) - 1| ≤ 3 / 2 * (1 / 3 ^ (k + 3)) :=
    (σ_close (m := k + 3) (by omega)).trans (le_of_eq (by ring))
  have hN : ((k + 3 : ℕ) : ℝ) = (k : ℝ) + 3 := by push_cast; ring
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hεn : 1 / 3 ^ (k + 3) * ((k + 3 : ℕ) : ℝ) ≤ 1 := by
    have h := three_pow_ge (k + 3)
    rw [div_mul_eq_mul_div, one_mul, div_le_one (by positivity)]
    nlinarith
  have hden : (((k + 1 : ℕ) : ℝ) + 1) * (((k + 1 : ℕ) : ℝ) + 2) =
      (((k + 3 : ℕ) : ℝ) - 1) * ((k + 3 : ℕ) : ℝ) := by push_cast; ring
  rw [hden]
  apply main_alg r_pos hp1 hp2 hq1 hq2 hpε hqε hεn (by rw [hN]; linarith)
  · split_ifs <;> positivity
  · rw [hN]; push_cast; split_ifs <;> linarith
  · rw [hN]; push_cast
    split_ifs <;> rw [abs_le] <;> constructor <;> linarith

/-! ### Theorem 2 -/

/-- The error term `g(n)/a_n - 1 - π⁴/(48n)`. -/
noncomputable def R (n : ℕ) : ℝ := (g n : ℝ) * n ! / (E n : ℝ) ^ 2 - 1 - Real.pi ^ 4 / (48 * n)

theorem pi4_eq : Real.pi ^ 4 / 48 = r ^ 2 / 3 := by unfold r; ring

theorem R_bound_large (h1 : StanleyGF) (k : ℕ) :
    |R (k + 3)| ≤ (362 * r ^ 2 + 36 * r ^ 4 * Real.exp (2 * r ^ 2)) / ((k + 3 : ℕ) : ℝ) ^ 2 := by
  set n := k + 3 with hn
  have hnpos : (0 : ℝ) < n := by positivity
  have han := a_pos n
  -- g/a_n as a sum
  have hsum : (g n : ℝ) * n ! / (E n : ℝ) ^ 2 = ∑ m ∈ range (n + 1), a m / a n * cc n m := by
    have : (g n : ℝ) * n ! / (E n : ℝ) ^ 2 = g n / a n := by
      unfold a; rw [div_div_eq_mul_div]
    rw [this, h1 n, Finset.sum_div]
    exact Finset.sum_congr rfl fun m _ => by ring
  have hsplit : ∑ m ∈ range (n + 1), a m / a n * cc n m =
      ∑ m ∈ range (k + 1), a m / a n * cc n m + a (k + 1) / a n * cc n (k + 1) + 0 + 1 := by
    rw [show n + 1 = k + 1 + 1 + 1 + 1 by omega, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ]
    rw [show k + 1 + 1 + 1 = n by omega, cc_self, div_self han.ne', one_mul,
      cc_odd (show ¬ Even (n - (k + 1 + 1)) by rw [show n - (k + 1 + 1) = 1 by omega]; decide),
      mul_zero]
  have ht := tail_sum k
  have hm := main_term k
  have ht0 : 0 ≤ ∑ m ∈ range (k + 1), a m / a n * cc n m :=
    Finset.sum_nonneg fun m _ => mul_nonneg (div_nonneg (a_pos m).le han.le) (cc_nonneg _ _)
  have hR : R n = ∑ m ∈ range (k + 1), a m / a n * cc n m +
      (a (k + 1) / a n * cc n (k + 1) - r ^ 2 / (3 * (n : ℝ))) := by
    unfold R
    rw [hsum, hsplit, show Real.pi ^ 4 / (48 * (n : ℝ)) = r ^ 2 / (3 * n) by
      unfold r; field_simp; ring]
    ring
  rw [hR]
  have hx : (2 * r ^ 2 / (n : ℝ)) ^ 2 = 4 * r ^ 4 / (n : ℝ) ^ 2 := by field_simp; ring
  have hexp : Real.exp (2 * r ^ 2 / (n : ℝ)) ≤ Real.exp (2 * r ^ 2) := by
    apply Real.exp_le_exp.mpr
    rw [div_le_iff₀ hnpos]
    have : (1 : ℝ) ≤ n := by rw [hn]; push_cast; linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
    nlinarith [r_pos]
  rw [hx] at ht
  calc |∑ m ∈ range (k + 1), a m / a n * cc n m +
        (a (k + 1) / a n * cc n (k + 1) - r ^ 2 / (3 * (n : ℝ)))|
      ≤ |∑ m ∈ range (k + 1), a m / a n * cc n m| +
        |a (k + 1) / a n * cc n (k + 1) - r ^ 2 / (3 * (n : ℝ))| := abs_add_le _ _
    _ ≤ 9 * (4 * r ^ 4 / (n : ℝ) ^ 2) * Real.exp (2 * r ^ 2) + 362 * r ^ 2 / (n : ℝ) ^ 2 := by
        rw [abs_of_nonneg ht0]
        exact add_le_add (ht.trans (by gcongr)) hm
    _ = (362 * r ^ 2 + 36 * r ^ 4 * Real.exp (2 * r ^ 2)) / (n : ℝ) ^ 2 := by ring

/-- **Theorem 2 of the paper** (conditional on Stanley's generating function): `g(n) n!/E_n² = 1 + π⁴/(48n) + O(n⁻²)`. -/
theorem g_asymp (h1 : StanleyGF) :
    ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n →
      |(g n : ℝ) * n ! / (E n : ℝ) ^ 2 - 1 - Real.pi ^ 4 / (48 * n)| ≤ C / (n : ℝ) ^ 2 := by
  set C0 := 362 * r ^ 2 + 36 * r ^ 4 * Real.exp (2 * r ^ 2)
  refine ⟨max C0 (max (|R 1|) (4 * |R 2|)), fun n hn => ?_⟩
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  rw [le_div_iff₀ (by positivity)]
  change |R n| * (n : ℝ) ^ 2 ≤ _
  rcases (show n = 1 ∨ n = 2 ∨ 3 ≤ n by omega) with rfl | rfl | h3
  · rw [show |R 1| * ((1 : ℕ) : ℝ) ^ 2 = |R 1| by push_cast; ring]
    exact le_trans (le_max_left _ _) (le_max_right _ _)
  · rw [show |R 2| * ((2 : ℕ) : ℝ) ^ 2 = 4 * |R 2| by push_cast; ring]
    exact le_trans (le_max_right _ _) (le_max_right _ _)
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
    have h := R_bound_large h1 k
    rw [le_div_iff₀ (by positivity)] at h
    exact h.trans (le_max_left _ _)

/-- Theorem 2, second form: `g(n) = (16/π²) (4/π²)ⁿ n! (1 + π⁴/(48n) + O(n⁻²))`. -/
theorem g_asymp' (h1 : StanleyGF) :
    ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n →
      |(g n : ℝ) / (16 / Real.pi ^ 2 * (4 / Real.pi ^ 2) ^ n * n !) - 1 -
        Real.pi ^ 4 / (48 * n)| ≤ C / (n : ℝ) ^ 2 := by
  obtain ⟨C, hC⟩ := g_asymp h1
  refine ⟨16 + 5 * C, fun n hn => ?_⟩
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hR := hC n hn
  set t := Real.pi ^ 4 / (48 * (n : ℝ))
  set G := (g n : ℝ) * n ! / (E n : ℝ) ^ 2
  obtain ⟨hs1, hs2⟩ := σ_bounds hn
  have hsc := σ_close hn
  -- `g / main = G σ²`
  have hmain : (g n : ℝ) / (16 / Real.pi ^ 2 * (4 / Real.pi ^ 2) ^ n * n !) = G * σ n ^ 2 := by
    have ha := a_formula hn
    have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
    have h16 : (16 / Real.pi ^ 2 * (4 / Real.pi ^ 2) ^ n : ℝ) = 4 / r ^ (n + 1) := by
      unfold r; rw [pow_succ, div_pow, div_pow]; field_simp; ring
    have hrp : 0 < r ^ (n + 1) := pow_pos r_pos _
    have hfa : (16 / Real.pi ^ 2 * (4 / Real.pi ^ 2) ^ n * n ! : ℝ) * σ n ^ 2 = a n := by
      rw [ha, h16]; field_simp
    have hG : G = g n / a n := by unfold a; simp only [G]; rw [div_div_eq_mul_div]
    rw [hG, ← hfa]
    have hs0 : 0 < σ n := by linarith
    have hm : (0 : ℝ) < 16 / Real.pi ^ 2 * (4 / Real.pi ^ 2) ^ n * n ! := by
      have := Real.pi_pos; have : (0 : ℝ) < n ! := by exact_mod_cast Nat.factorial_pos n
      positivity
    field_simp [hm.ne', hs0.ne']
  rw [hmain]
  have hC0 : 0 ≤ C := by
    have := (abs_nonneg _).trans hR
    rwa [le_div_iff₀ (by positivity), zero_mul] at this
  have hRabs : |G - 1 - t| ≤ C := by
    refine hR.trans ?_
    rw [div_le_iff₀ (by positivity)]
    have hn2 : (1 : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hn2 hC0]
  have ht0 : 0 ≤ t := by positivity
  have ht3 : t ≤ 3 := by
    simp only [t]
    rw [div_le_iff₀ (by positivity)]
    have h10 := pi_sq_lt
    have hp2 : 0 < Real.pi ^ 2 := by positivity
    have : Real.pi ^ 4 < 100 := by
      have : Real.pi ^ 4 = (Real.pi ^ 2) ^ 2 := by ring
      rw [this]; nlinarith
    nlinarith
  have hσ2 : |σ n ^ 2 - 1| ≤ 4 / (n : ℝ) ^ 2 := by
    have h3n := three_pow_ge n
    have : |σ n ^ 2 - 1| ≤ 4 / 3 ^ n := by
      rw [show σ n ^ 2 - 1 = (σ n - 1) * (σ n + 1) by ring, abs_mul,
        abs_of_pos (by linarith : (0 : ℝ) < σ n + 1)]
      calc |σ n - 1| * (σ n + 1) ≤ 3 / 2 / 3 ^ n * (5 / 2) := by
            apply mul_le_mul hsc (by linarith) (by linarith) (by positivity)
        _ ≤ 4 / 3 ^ n := by rw [div_mul_eq_mul_div]; gcongr; norm_num
    exact this.trans (by gcongr)
  have hexp : G * σ n ^ 2 - 1 - t = (σ n ^ 2 - 1) * (1 + t + (G - 1 - t)) + (G - 1 - t) := by ring
  rw [hexp]
  calc |(σ n ^ 2 - 1) * (1 + t + (G - 1 - t)) + (G - 1 - t)|
      ≤ |σ n ^ 2 - 1| * |1 + t + (G - 1 - t)| + |G - 1 - t| := by
        rw [← abs_mul]; exact abs_add_le _ _
    _ ≤ 4 / (n : ℝ) ^ 2 * (4 + C) + C / (n : ℝ) ^ 2 := by
        gcongr
        calc |1 + t + (G - 1 - t)| ≤ |1 + t| + |G - 1 - t| := abs_add_le _ _
          _ ≤ 4 + C := by rw [abs_of_nonneg (by linarith)]; linarith
    _ = (16 + 5 * C) / (n : ℝ) ^ 2 := by ring

end Alt

end Stanley
