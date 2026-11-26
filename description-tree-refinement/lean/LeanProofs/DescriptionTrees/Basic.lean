import Mathlib

/-!
# The description-tree refinement of A336110: key lemmas

The note proves Voloshyn's conjecture (OEIS A336110): the unsigned numerator coefficients of the
Gross–Witten–Wadia rational functions `P_s` count the description trees of type `(2,2)` with `s`
edges by the statistic `ν`. Its proof runs through one hypergeometric term

  `Ω(k, m) = 12^k / ((k+1)! (2k+1)!) * ∏_{L=1}^{k} C(m+2L, 3)`.

This file formalises the lemmas of the note that concern `Ω` and the parametrisation:

* `Om_succ`: the three-term recurrence `(k+2)(2k+2)(2k+3) Ω(k+1,m) = 2(m+2k+2)(m+2k+1)(m+2k) Ω(k,m)`.
  In the note this is the coefficient of `y^{k+1} z^m` in the differential equation `𝓛 H = 0`
  (Step 3), since `θ_z z^m = m z^m`.
* `coeff_unique`: two arrays satisfying that recurrence and agreeing at `k = 0` agree everywhere
  (the uniqueness step of Step 3, at the level of coefficients).
* `lemma2_odd`, `lemma2_even` (Lemma 2): `Ω(s, 2r+1) = C_s a_r` and `Ω(s, 2r+2) = 4^s b_r`, where
  `a_r`, `b_r` are the coefficients of the two `₃F₂` series in the definition of `P_s`, written with
  Mathlib's rising factorials `ascPochhammer`.
* `quartic_param`: the parametrisation `(t*, q*)` of Step 2 solves the quartic `R(q, t) = 0`.

Not formalised here (SymPy certificates in `verify/`): the catalytic equation for actual trees, the
existence of the double root `U` and the resultant factorisation, and the identity `𝓛 H = 0`.
-/

set_option linter.style.longLine false

open Finset

namespace DescriptionTrees

/-- `Ω(k, m) = 12^k / ((k+1)! (2k+1)!) * ∏_{L=1}^{k} C(m+2L, 3)`. -/
def Om (k m : ℕ) : ℚ :=
  (12 : ℚ) ^ k / (((k + 1).factorial : ℚ) * ((2 * k + 1).factorial : ℚ)) *
    ∏ L ∈ range k, (((m + 2 * (L + 1)).choose 3 : ℕ) : ℚ)

lemma choose_three (a : ℕ) :
    (((a + 2).choose 3 : ℕ) : ℚ) = ((a : ℚ) + 2) * ((a : ℚ) + 1) * (a : ℚ) / 6 := by
  have h := Nat.descFactorial_eq_factorial_mul_choose (a + 2) 3
  simp [Nat.descFactorial_succ, Nat.factorial] at h
  have : ((a + 2).choose 3 : ℚ) * 6 = ((a : ℚ) + 2) * ((a : ℚ) + 1) * (a : ℚ) := by
    have h' : ((a + 2 - 2) * ((a + 2 - 1) * (a + 2)) : ℕ) = 6 * (a + 2).choose 3 := by
      simpa [mul_comm, mul_assoc, mul_left_comm] using h
    have e1 : (a + 2 - 2) = a := by omega
    have e2 : (a + 2 - 1) = a + 1 := by omega
    rw [e1, e2] at h'
    have := congrArg (fun n : ℕ => (n : ℚ)) h'
    push_cast at this
    linarith
  linarith

/-- The recurrence of `Ω` in `k` (the coefficient form of `𝓛 H = 0`). -/
theorem Om_succ (k m : ℕ) :
    ((k : ℚ) + 2) * (2 * k + 2) * (2 * k + 3) * Om (k + 1) m =
      2 * ((m : ℚ) + 2 * k + 2) * (m + 2 * k + 1) * (m + 2 * k) * Om k m := by
  unfold Om
  rw [prod_range_succ]
  have hc : m + 2 * (k + 1) = (m + 2 * k) + 2 := by ring
  rw [hc, choose_three]
  have f1 : ((k + 1 + 1).factorial : ℚ) = ((k : ℚ) + 2) * (k + 1).factorial := by
    rw [Nat.factorial_succ]; push_cast; ring
  have f2 : ((2 * (k + 1) + 1).factorial : ℚ) = ((2 * k : ℚ) + 3) * (2 * k + 2) * (2 * k + 1).factorial := by
    have : 2 * (k + 1) + 1 = (2 * k + 1) + 1 + 1 := by ring
    rw [this, Nat.factorial_succ, Nat.factorial_succ]; push_cast; ring
  rw [f1, f2]
  have : ((k + 1).factorial : ℚ) ≠ 0 := by positivity
  have : ((2 * k + 1).factorial : ℚ) ≠ 0 := by positivity
  push_cast
  field_simp
  ring

/-- Uniqueness: the recurrence of `Om_succ` and the row `k = 0` determine the array. -/
theorem coeff_unique (c d : ℕ → ℕ → ℚ)
    (hc : ∀ k m : ℕ, ((k : ℚ) + 2) * (2 * k + 2) * (2 * k + 3) * c (k + 1) m =
      2 * ((m : ℚ) + 2 * k + 2) * (m + 2 * k + 1) * (m + 2 * k) * c k m)
    (hd : ∀ k m : ℕ, ((k : ℚ) + 2) * (2 * k + 2) * (2 * k + 3) * d (k + 1) m =
      2 * ((m : ℚ) + 2 * k + 2) * (m + 2 * k + 1) * (m + 2 * k) * d k m)
    (h0 : ∀ m, c 0 m = d 0 m) : c = d := by
  funext k m
  induction k with
  | zero => exact h0 m
  | succ k ih =>
    have hne : ((k : ℚ) + 2) * (2 * k + 2) * (2 * k + 3) ≠ 0 := by positivity
    apply mul_left_cancel₀ hne
    rw [hc, hd, ih]

theorem Om_zero (m : ℕ) : Om 0 m = 1 := by simp [Om]

/-! ### Lemma 2: the two hypergeometric series -/

/-- Rising factorial `(x)_r`. -/
noncomputable def rf (x : ℚ) (r : ℕ) : ℚ := (ascPochhammer ℚ r).eval x

/-- Coefficient of `X^r` in `₃F₂[s+1/2, s+1, s+3/2; 1/2, 3/2; X]`. -/
noncomputable def a (s r : ℕ) : ℚ :=
  rf ((s : ℚ) + 1 / 2) r * rf ((s : ℚ) + 1) r * rf ((s : ℚ) + 3 / 2) r /
    (rf (1 / 2) r * rf (3 / 2) r * r.factorial)

/-- Coefficient of `X^r` in `₃F₂[s+1, s+3/2, s+2; 3/2, 2; X]`. -/
noncomputable def b (s r : ℕ) : ℚ :=
  rf ((s : ℚ) + 1) r * rf ((s : ℚ) + 3 / 2) r * rf ((s : ℚ) + 2) r /
    (rf (3 / 2) r * rf 2 r * r.factorial)

lemma rf_shift (x : ℚ) (n : ℕ) : x * rf (x + 1) n = rf x n * (x + n) := by
  have h1 := congrArg (Polynomial.eval x) (ascPochhammer_succ_left ℚ n)
  have h2 := ascPochhammer_succ_eval (S := ℚ) n x
  simp [Polynomial.eval_comp] at h1
  simp only [rf]
  rw [← h1, h2]

lemma rf_pos {x : ℚ} (hx : 0 < x) (n : ℕ) : 0 < rf x n := ascPochhammer_pos n x hx

lemma rf_one (n : ℕ) : rf 1 n = n.factorial := by simp [rf, ascPochhammer_eval_one]

lemma catalan_succ_ratio (n : ℕ) : ((n : ℚ) + 2) * catalan (n + 1) = 2 * (2 * n + 1) * catalan n := by
  have h1 := succ_mul_catalan_eq_centralBinom (n + 1)
  have h2 := succ_mul_catalan_eq_centralBinom n
  have h3 := Nat.succ_mul_centralBinom_succ n
  have : ((n + 1 : ℕ) : ℚ) * (((n : ℚ) + 2) * catalan (n + 1)) =
      ((n + 1 : ℕ) : ℚ) * (2 * (2 * n + 1) * catalan n) := by
    have e1 : ((n + 2 : ℕ) : ℚ) * catalan (n + 1) = (Nat.centralBinom (n + 1) : ℚ) := by exact_mod_cast h1
    have e2 : ((n + 1 : ℕ) : ℚ) * catalan n = (Nat.centralBinom n : ℚ) := by exact_mod_cast h2
    have e3 : ((n + 1 : ℕ) : ℚ) * Nat.centralBinom (n + 1) = 2 * (2 * n + 1) * (Nat.centralBinom n : ℚ) := by
      exact_mod_cast h3
    push_cast at e1 e2 e3 ⊢
    nlinarith [e1, e2, e3]
  have hn : ((n + 1 : ℕ) : ℚ) ≠ 0 := by positivity
  exact mul_left_cancel₀ hn this

/-- Lemma 2, odd part: `Ω(s, 2r+1) = C_s a_r`. -/
theorem lemma2_odd (s r : ℕ) : Om s (2 * r + 1) = catalan s * a s r := by
  induction s with
  | zero =>
    rw [Om_zero]
    simp only [a, rf_one, catalan_zero, Nat.cast_one, Nat.cast_zero, zero_add, one_mul]
    have h1 : 0 < rf (1 / 2) r := rf_pos (by norm_num) r
    have h2 : 0 < rf (3 / 2) r := rf_pos (by norm_num) r
    have h3 : (0 : ℚ) < r.factorial := by positivity
    field_simp
  | succ s ih =>
    have hrec := Om_succ s (2 * r + 1)
    have hcat := catalan_succ_ratio s
    have hs1 := rf_shift ((s : ℚ) + 1 / 2) r
    have hs2 := rf_shift ((s : ℚ) + 1) r
    have hs3 := rf_shift ((s : ℚ) + 3 / 2) r
    have p1 : 0 < rf (1 / 2) r := rf_pos (by norm_num) r
    have p2 : 0 < rf (3 / 2) r := rf_pos (by norm_num) r
    have p3 : (0 : ℚ) < r.factorial := by positivity
    have hne : ((s : ℚ) + 2) * (2 * s + 2) * (2 * s + 3) ≠ 0 := by positivity
    apply mul_left_cancel₀ hne
    rw [hrec, ih]
    simp only [a] at *
    push_cast at *
    have q1 : ((s : ℚ) + 1 / 2) ≠ 0 := by positivity
    have q2 : ((s : ℚ) + 1) ≠ 0 := by positivity
    have q3 : ((s : ℚ) + 3 / 2) ≠ 0 := by positivity
    have e1 : rf ((s : ℚ) + 1 + 1 / 2) r = rf ((s : ℚ) + 1 / 2) r * ((s : ℚ) + 1 / 2 + r) / ((s : ℚ) + 1 / 2) := by
      rw [eq_div_iff q1, ← hs1]; ring_nf
    have e2 : rf ((s : ℚ) + 1 + 1) r = rf ((s : ℚ) + 1) r * ((s : ℚ) + 1 + r) / ((s : ℚ) + 1) := by
      rw [eq_div_iff q2, ← hs2]; ring_nf
    have e3 : rf ((s : ℚ) + 1 + 3 / 2) r = rf ((s : ℚ) + 3 / 2) r * ((s : ℚ) + 3 / 2 + r) / ((s : ℚ) + 3 / 2) := by
      rw [eq_div_iff q3, ← hs3]; ring_nf
    rw [e1, e2, e3]
    have hc' : (catalan (s + 1) : ℚ) = 2 * (2 * s + 1) * catalan s / ((s : ℚ) + 2) := by
      rw [eq_div_iff (by positivity)]; linarith [hcat]
    rw [hc']
    field_simp
    ring

/-- Lemma 2, even part: `Ω(s, 2r+2) = 4^s b_r`. -/
theorem lemma2_even (s r : ℕ) : Om s (2 * r + 2) = 4 ^ s * b s r := by
  induction s with
  | zero =>
    rw [Om_zero]
    simp only [b, rf_one, pow_zero, Nat.cast_zero, zero_add, one_mul]
    have h1 : 0 < rf 2 r := rf_pos (by norm_num) r
    have h2 : 0 < rf (3 / 2) r := rf_pos (by norm_num) r
    have h3 : (0 : ℚ) < r.factorial := by positivity
    field_simp
  | succ s ih =>
    have hrec := Om_succ s (2 * r + 2)
    have hs1 := rf_shift ((s : ℚ) + 1) r
    have hs2 := rf_shift ((s : ℚ) + 3 / 2) r
    have hs3 := rf_shift ((s : ℚ) + 2) r
    have p1 : 0 < rf 2 r := rf_pos (by norm_num) r
    have p2 : 0 < rf (3 / 2) r := rf_pos (by norm_num) r
    have p3 : (0 : ℚ) < r.factorial := by positivity
    have hne : ((s : ℚ) + 2) * (2 * s + 2) * (2 * s + 3) ≠ 0 := by positivity
    apply mul_left_cancel₀ hne
    rw [hrec, ih]
    simp only [b] at *
    push_cast at *
    have q1 : ((s : ℚ) + 1) ≠ 0 := by positivity
    have q2 : ((s : ℚ) + 3 / 2) ≠ 0 := by positivity
    have q3 : ((s : ℚ) + 2) ≠ 0 := by positivity
    have e1 : rf ((s : ℚ) + 1 + 1) r = rf ((s : ℚ) + 1) r * ((s : ℚ) + 1 + r) / ((s : ℚ) + 1) := by
      rw [eq_div_iff q1, ← hs1]; ring_nf
    have e2 : rf ((s : ℚ) + 1 + 3 / 2) r = rf ((s : ℚ) + 3 / 2) r * ((s : ℚ) + 3 / 2 + r) / ((s : ℚ) + 3 / 2) := by
      rw [eq_div_iff q2, ← hs2]; ring_nf
    have e3 : rf ((s : ℚ) + 1 + 2) r = rf ((s : ℚ) + 2) r * ((s : ℚ) + 2 + r) / ((s : ℚ) + 2) := by
      rw [eq_div_iff q3, ← hs3]; ring_nf
    rw [e1, e2, e3]
    field_simp
    ring

/-! ### Step 2: the parametrisation solves the quartic -/

/-- The quartic factor `R(q, t)` of the resultant in Step 2 (coefficients in `ℤ[z, t]`). -/
def R (z t q : ℚ) : ℚ :=
  16 * t ^ 3 * (z - 1) ^ 2 * q ^ 4
  + 8 * t ^ 2 * (4 * t * z ^ 3 - 4 * t * z ^ 2 - 4 * t * z + 4 * t + z ^ 2 - 4 * z + 1) * q ^ 3
  + t * (16 * t ^ 2 * z ^ 4 + 32 * t ^ 2 * z ^ 3 - 96 * t ^ 2 * z ^ 2 + 32 * t ^ 2 * z + 16 * t ^ 2
      - 8 * t * z ^ 3 - 16 * t * z ^ 2 - 16 * t * z - 8 * t + z ^ 2 - 10 * z + 1) * q ^ 2
  + z * (32 * t ^ 3 * z ^ 3 - 32 * t ^ 3 * z ^ 2 - 32 * t ^ 3 * z + 32 * t ^ 3 - 32 * t ^ 2 * z ^ 2
      + 16 * t ^ 2 * z - 32 * t ^ 2 + 10 * t * z + 10 * t - 1) * q
  + t * z ^ 2 * (16 * t ^ 2 * z ^ 2 - 32 * t ^ 2 * z + 16 * t ^ 2 - 8 * t * z - 8 * t + 1)

/-- At `t = 0` the quartic is `-z q`, so its series root through `q = 0` is unique. -/
theorem R_at_zero (z q : ℚ) : R z 0 q = -z * q := by simp [R]

/-- `R` with `t = N₁/D₁`, `q = N₂/D₂`, multiplied by `D₁³ D₂⁴`. -/
def Rh (z N1 D1 N2 D2 : ℚ) : ℚ :=
    (16*(z - 1) ^ 2) * N1 ^ 3 * D1 ^ 0 * N2 ^ 4 * D2 ^ 0 +
    (32*(z - 1) ^ 2*(z + 1)) * N1 ^ 3 * D1 ^ 0 * N2 ^ 3 * D2 ^ 1 +
    (16*(z - 1) ^ 2*(z ^ 2 + 4*z + 1)) * N1 ^ 3 * D1 ^ 0 * N2 ^ 2 * D2 ^ 2 +
    (32*z*(z - 1) ^ 2*(z + 1)) * N1 ^ 3 * D1 ^ 0 * N2 ^ 1 * D2 ^ 3 +
    (16*z ^ 2*(z - 1) ^ 2) * N1 ^ 3 * D1 ^ 0 * N2 ^ 0 * D2 ^ 4 +
    (8*(z ^ 2 - 4*z + 1)) * N1 ^ 2 * D1 ^ 1 * N2 ^ 3 * D2 ^ 1 +
    (-8*(z + 1)*(z ^ 2 + z + 1)) * N1 ^ 2 * D1 ^ 1 * N2 ^ 2 * D2 ^ 2 +
    (-16*z*(2*z ^ 2 - z + 2)) * N1 ^ 2 * D1 ^ 1 * N2 ^ 1 * D2 ^ 3 +
    (-8*z ^ 2*(z + 1)) * N1 ^ 2 * D1 ^ 1 * N2 ^ 0 * D2 ^ 4 +
    (z ^ 2 - 10*z + 1) * N1 ^ 1 * D1 ^ 2 * N2 ^ 2 * D2 ^ 2 +
    (10*z*(z + 1)) * N1 ^ 1 * D1 ^ 2 * N2 ^ 1 * D2 ^ 3 +
    (z ^ 2) * N1 ^ 1 * D1 ^ 2 * N2 ^ 0 * D2 ^ 4 +
    (-z) * N1 ^ 0 * D1 ^ 3 * N2 ^ 1 * D2 ^ 3

lemma R_div (z N1 D1 N2 D2 : ℚ) (h1 : D1 ≠ 0) (h2 : D2 ≠ 0) :
    R z (N1 / D1) (N2 / D2) = Rh z N1 D1 N2 D2 / (D1 ^ 3 * D2 ^ 4) := by
  unfold R Rh
  field_simp
  ring

/-- Numerator and denominator of `t* = p(1-p)²(1+pz) / ((1+p)²(1-p+2pz)²)`. -/
def tNum (p z : ℚ) : ℚ := p * (1 - p) ^ 2 * (1 + p * z)
def tDen (p z : ℚ) : ℚ := (1 + p) ^ 2 * (1 - p + 2 * p * z) ^ 2

/-- Numerator and denominator of `q* = zp((1-p)² - 4zp²) / ((1-p)²(1+pz))`. -/
def qNum (p z : ℚ) : ℚ := z * p * ((1 - p) ^ 2 - 4 * z * p ^ 2)
def qDen (p z : ℚ) : ℚ := (1 - p) ^ 2 * (1 + p * z)

def tStar (p z : ℚ) : ℚ := tNum p z / tDen p z
def qStar (p z : ℚ) : ℚ := qNum p z / qDen p z

set_option maxRecDepth 20000 in
/-- The rational parametrisation of Step 2 solves `R(q, t) = 0`. -/
theorem quartic_param (p z : ℚ) (h1 : 1 + p ≠ 0) (h2 : 1 - p ≠ 0) (h3 : 1 + p * z ≠ 0)
    (h4 : 1 - p + 2 * p * z ≠ 0) : R z (tStar p z) (qStar p z) = 0 := by
  have d1 : tDen p z ≠ 0 := by unfold tDen; positivity
  have d2 : qDen p z ≠ 0 := by unfold qDen; positivity
  unfold tStar qStar
  rw [R_div _ _ _ _ _ d1 d2]
  have : Rh z (tNum p z) (tDen p z) (qNum p z) (qDen p z) = 0 := by
    unfold Rh tNum tDen qNum qDen; ring
  rw [this, zero_div]

end DescriptionTrees
