import Mathlib
import LeanProofs.HitomezashiBiased.Continuant

/-!
# Biased hitomezashi loops: summing the series

The loop density is `c(p) = (1/4) ∑_k X p k ^ 2`. Splitting `k` into even and odd and writing `n = j + 1`,
the summand becomes a rational function of `n` whose partial fractions involve only
`∑ 1/n²`, `∑ 2/(n² - x²)` (the cotangent series, from Mathlib's Mittag-Leffler expansion) and
`∑ (1/(n+x)² + 1/(n-x)²)` (the cosecant-squared series, obtained here by differentiating the cotangent
series term by term).
-/

namespace HitomezashiBiased

open Real Filter Topology

/-- Real form of the Mittag-Leffler expansion of the cotangent, on `(0, 1)`. -/
theorem real_cot_series {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    HasSum (fun n : ℕ => 1 / (x - (n + 1)) + 1 / (x + (n + 1))) (π * Real.cot (π * x) - 1 / x) := by
  have hmem : (x : ℂ) ∈ Complex.integerComplement := by
    rw [Complex.mem_integerComplement_iff]
    rintro ⟨n, hn⟩
    have hn' : (n : ℝ) = x := by exact_mod_cast hn
    have h0 : (0 : ℝ) < n := hn' ▸ hx0
    have h1 : (n : ℝ) < 1 := hn' ▸ hx1
    norm_cast at h0 h1
    omega
  have hs := (summable_cotTerm hmem).hasSum
  have hrep := cot_series_rep' hmem
  simp only [cotTerm] at hs
  rw [← hrep] at hs
  rw [← Complex.hasSum_ofReal]
  convert hs using 1
  · ext n; push_cast; rfl
  · rw [Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_cot]; push_cast; rfl

/-- `∑_{n ≥ 1} 2/(n² - x²) = (1/x - π cot πx)/x` on `(0, 1)`. -/
theorem hasSum_K {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    HasSum (fun n : ℕ => 2 / (((n : ℝ) + 1) ^ 2 - x ^ 2)) ((1 / x - π * Real.cot (π * x)) / x) := by
  have h := (real_cot_series hx0 hx1).mul_left (-1 / x)
  convert h using 1
  · ext n
    have h1 : x - (n + 1) ≠ 0 := by have := n.cast_nonneg (α := ℝ); intro h; linarith
    have h2 : x + (n + 1) ≠ 0 := by positivity
    have h3 : ((n : ℝ) + 1) ^ 2 - x ^ 2 ≠ 0 := by
      have := n.cast_nonneg (α := ℝ); nlinarith
    field_simp
    ring
  · field_simp
    ring

theorem summable_inv_succ_sq : Summable (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 2) := by
  have := (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr one_lt_two)
  simpa using this

/-- Derivative of `π cot(π y) - 1/y`. -/
theorem hasDerivAt_cot_sub {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    HasDerivAt (fun y => π * Real.cot (π * y) - 1 / y)
      (-(π ^ 2 / Real.sin (π * x) ^ 2) + 1 / x ^ 2) x := by
  have hs : Real.sin (π * x) ≠ 0 :=
    (Real.sin_pos_of_pos_of_lt_pi (by positivity) (by nlinarith [pi_pos])).ne'
  have hsin : HasDerivAt (fun y => Real.sin (π * y)) (Real.cos (π * x) * π) x := by
    simpa using ((hasDerivAt_id x).const_mul π).sin
  have hcos : HasDerivAt (fun y => Real.cos (π * y)) (-Real.sin (π * x) * π) x := by
    simpa using ((hasDerivAt_id x).const_mul π).cos
  have hq := ((hcos.div hsin hs).const_mul π).sub ((hasDerivAt_id x).inv hx0.ne')
  have hfun : (fun y => π * Real.cot (π * y) - 1 / y) =
      (fun y => π * (Real.cos (π * y) / Real.sin (π * y)) - (id y)⁻¹) := by
    ext y; simp [Real.cot_eq_cos_div_sin, one_div]
  rw [hfun]
  convert hq using 1
  have num : -Real.sin (π * x) * π * Real.sin (π * x) - Real.cos (π * x) * (Real.cos (π * x) * π) = -π := by
    linear_combination (-π) * Real.sin_sq_add_cos_sq (π * x)
  simp only [id, num]
  field_simp
  ring

/-- `∑_{n ≥ 1} (1/(n+x)² + 1/(n-x)²) = π²/sin²(πx) - 1/x²` on `(0, 1)`, by differentiating the
cotangent series term by term. -/
theorem hasSum_T {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    HasSum (fun n : ℕ => 1 / (((n : ℝ) + 1) + x) ^ 2 + 1 / (((n : ℝ) + 1) - x) ^ 2)
      (π ^ 2 / Real.sin (π * x) ^ 2 - 1 / x ^ 2) := by
  set b : ℝ := (1 + x) / 2 with hb
  have hb1 : b < 1 := by rw [hb]; linarith
  have hxb : x < b := by rw [hb]; linarith
  let g : ℕ → ℝ → ℝ := fun n y => 1 / (y - (n + 1)) + 1 / (y + (n + 1))
  let g' : ℕ → ℝ → ℝ := fun n y => -(1 / (y - (n + 1)) ^ 2) - 1 / (y + (n + 1)) ^ 2
  let u : ℕ → ℝ := fun n => (1 / (1 - b) ^ 2 + 1) * (1 / ((n : ℝ) + 1) ^ 2)
  have hu : Summable u := summable_inv_succ_sq.mul_left _
  have hg : ∀ n y, y ∈ Set.Ioo 0 b → HasDerivAt (g n) (g' n y) y := by
    intro n y hy
    have hn := n.cast_nonneg (α := ℝ)
    have h1 : y - (n + 1) ≠ 0 := by intro h; linarith [hy.2]
    have h2 : y + (n + 1) ≠ 0 := by intro h; linarith [hy.1]
    have d1 := ((hasDerivAt_id y).sub_const ((n : ℝ) + 1)).inv h1
    have d2 := ((hasDerivAt_id y).add_const ((n : ℝ) + 1)).inv h2
    convert d1.add d2 using 1
    · ext z; simp [g, one_div]
    · simp [g', one_div]; ring
  have hg' : ∀ n y, y ∈ Set.Ioo 0 b → ‖g' n y‖ ≤ u n := by
    intro n y hy
    have hn := n.cast_nonneg (α := ℝ)
    have hA : (1 - b) * ((n : ℝ) + 1) ≤ (n + 1) - y := by nlinarith [hy.2, hy.1]
    have hA0 : 0 < (1 - b) * ((n : ℝ) + 1) := by apply mul_pos <;> linarith
    have e1 : 1 / (y - (n + 1)) ^ 2 ≤ 1 / (1 - b) ^ 2 * (1 / ((n : ℝ) + 1) ^ 2) := by
      rw [show (y - (n + 1)) ^ 2 = ((n + 1) - y) ^ 2 by ring, one_div_mul_one_div, ← mul_pow]
      exact one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ hA0.le hA 2)
    have e2 : 1 / (y + (n + 1)) ^ 2 ≤ 1 / ((n : ℝ) + 1) ^ 2 :=
      one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ (by positivity) (by linarith [hy.1]) 2)
    have p1 : 0 ≤ 1 / (y - (n + 1)) ^ 2 := by positivity
    have p2 : 0 ≤ 1 / (y + (n + 1)) ^ 2 := by positivity
    simp only [g', u, Real.norm_eq_abs]
    rw [abs_le]
    constructor <;> nlinarith
  have hxt : x ∈ Set.Ioo 0 b := ⟨hx0, hxb⟩
  have hg0 : Summable fun n => g n x := (real_cot_series hx0 hx1).summable
  have hD := hasDerivAt_tsum_of_isPreconnected hu isOpen_Ioo isPreconnected_Ioo hg hg' hxt hg0 hxt
  have hev : (fun y => π * Real.cot (π * y) - 1 / y) =ᶠ[𝓝 x] (fun z => ∑' n, g n z) := by
    filter_upwards [Ioo_mem_nhds hx0 hx1] with y hy
    exact ((real_cot_series hy.1 hy.2).tsum_eq).symm
  have hval := (hD.congr_of_eventuallyEq hev).unique (hasDerivAt_cot_sub hx0 hx1)
  have hsum : HasSum (fun n => g' n x) (∑' n, g' n x) :=
    (hu.of_norm_bounded (fun n => hg' n x hxt)).hasSum
  rw [hval] at hsum
  convert hsum.neg using 1
  · ext n; simp only [g']; ring
  · ring

theorem hasSum_inv_succ_sq : HasSum (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 2) (π ^ 2 / 6) := by
  have := (hasSum_nat_add_iff' 1).mpr hasSum_zeta_two
  simpa using this

/-- The term-wise partial-fraction identity behind the main theorem, in the variable `n = j + 1`. -/
theorem term_identity (n p q : ℝ) (hn : n ≠ 0) (h1 : n - p ≠ 0) (h2 : n + p ≠ 0) (h3 : n - q ≠ 0)
    (h4 : n + q ≠ 0) (h5 : q - p ≠ 0) :
    (p * q / n * (p / (n - p) + q / (n - q))) ^ 2 / 4 + (p * q / n * (q / (n + q) + p / (n + p))) ^ 2 / 4 =
      ((p * q) ^ 2 / 4) * (8 * (1 / n ^ 2) + (1 / (n + p) ^ 2 + 1 / (n - p) ^ 2) +
        (1 / (n + q) ^ 2 + 1 / (n - q) ^ 2) + (-4 - 2 * p / (q - p)) * (2 / ((n - p) * (n + p))) +
        (-4 + 2 * q / (q - p)) * (2 / ((n - q) * (n + q)))) := by
  field_simp
  ring

/-- The same identity at `p = q = 1/2`. -/
theorem term_identity_half (n : ℝ) (hn : n ≠ 0) (h1 : n - 1 / 2 ≠ 0) (h2 : n + 1 / 2 ≠ 0) :
    (1 / 4 / n * (1 / 2 / (n - 1 / 2) + 1 / 2 / (n - 1 / 2))) ^ 2 / 4 +
      (1 / 4 / n * (1 / 2 / (n + 1 / 2) + 1 / 2 / (n + 1 / 2))) ^ 2 / 4 =
      (1 / 64) * (8 * (1 / n ^ 2) + 4 * (1 / (n + 1 / 2) ^ 2 + 1 / (n - 1 / 2) ^ 2) -
        8 * (2 / ((n - 1 / 2) * (n + 1 / 2)))) := by
  obtain ⟨c, rfl⟩ : ∃ c : ℝ, n = c / 2 := ⟨2 * n, by ring⟩
  rw [show c / 2 - 1 / 2 = (c - 1) / 2 by ring, show c / 2 + 1 / 2 = (c + 1) / 2 by ring] at *
  have hc : c ≠ 0 := by intro h; apply hn; rw [h]; norm_num
  have hc1 : c - 1 ≠ 0 := by intro h; apply h1; rw [h]; norm_num
  have hc2 : c + 1 ≠ 0 := by intro h; apply h2; rw [h]; norm_num
  field_simp
  ring

/-- The closing algebra: the sum of the five elementary series equals the closed form
(`s = sin πp`, `c = cos πp`, `P = π`; `sin π(1-p) = s`, `cos π(1-p) = -c`). -/
theorem value_eq (p s c P : ℝ) (hp0 : p ≠ 0) (hq0 : 1 - p ≠ 0) (hs : s ≠ 0) (h12 : 1 - 2 * p ≠ 0) :
    (p * (1 - p)) ^ 2 / 4 * (8 * (P ^ 2 / 6) + (P ^ 2 / s ^ 2 - 1 / p ^ 2) +
      (P ^ 2 / s ^ 2 - 1 / (1 - p) ^ 2) + (-4 - 2 * p / (1 - p - p)) * ((1 / p - P * (c / s)) / p) +
      (-4 + 2 * (1 - p) / (1 - p - p)) * ((1 / (1 - p) - P * (-c / s)) / (1 - p))) =
    2 * p * (1 - p) - 5 / 4 + P ^ 2 * (p * (1 - p)) ^ 2 / 6 * (2 + 3 / s ^ 2) +
      P * p * (1 - p) * (1 - 3 * p * (1 - p)) * (c / s) / (1 - 2 * p) := by
  rw [show 1 - p - p = 1 - 2 * p by ring]
  obtain ⟨d, hd⟩ : ∃ d, d = 1 - 2 * p := ⟨_, rfl⟩
  rw [← hd] at h12 ⊢
  have hpd : p = (1 - d) / 2 := by rw [hd]; ring
  subst hpd
  have h1 : 1 - d ≠ 0 := by intro h; apply hp0; rw [h]; norm_num
  have h2 : 1 + d ≠ 0 := by intro h; apply hq0; rw [show d = -1 by linarith]; norm_num
  rw [show 1 - (1 - d) / 2 = (1 + d) / 2 by ring]
  field_simp
  ring

/-- The closed form of the biased loop density (for `p ≠ 1/2`). -/
noncomputable def density (p : ℝ) : ℝ :=
  2 * p * (1 - p) - 5 / 4 + π ^ 2 * (p * (1 - p)) ^ 2 / 6 * (2 + 3 / Real.sin (π * p) ^ 2) +
    π * p * (1 - p) * (1 - 3 * p * (1 - p)) * Real.cot (π * p) / (1 - 2 * p)

private lemma sin_pos_of_unit {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) : 0 < Real.sin (π * x) :=
  Real.sin_pos_of_pos_of_lt_pi (by positivity) (by nlinarith [pi_pos])

/-- **Main theorem (series form).** For `0 < p < 1`, `p ≠ 1/2`, the loop density
`(1/4) ∑_k X p k ^ 2` of the `p`-biased random hitomezashi pattern equals `density p`. -/
theorem hasSum_density {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hp : p ≠ 1 / 2) :
    HasSum (fun k => X p k ^ 2 / 4) (density p) := by
  set q : ℝ := 1 - p with hq
  have hq0 : 0 < q := by rw [hq]; linarith
  have hq1 : q < 1 := by rw [hq]; linarith
  have hqp : q - p ≠ 0 := by rw [hq]; intro h; apply hp; linarith
  set c1 : ℝ := -4 - 2 * p / (q - p)
  set c2 : ℝ := -4 + 2 * q / (q - p)
  let T : ℝ → ℕ → ℝ := fun x n => 1 / (((n : ℝ) + 1) + x) ^ 2 + 1 / (((n : ℝ) + 1) - x) ^ 2
  let K : ℝ → ℕ → ℝ := fun x n => 2 / (((n : ℝ) + 1) ^ 2 - x ^ 2)
  have term : ∀ j : ℕ, X p (2 * j) ^ 2 / 4 + X p (2 * j + 1) ^ 2 / 4 =
      ((p * q) ^ 2 / 4) * (8 * (1 / ((j : ℝ) + 1) ^ 2) + T p j + T q j + c1 * K p j + c2 * K q j) := by
    intro j
    have hj := j.cast_nonneg (α := ℝ)
    rw [X_even hp0 hp1, X_odd hp0 hp1]
    simp only [T, K, c1, c2]
    rw [show (j : ℝ) + (1 - p) = ((j : ℝ) + 1) - p by ring, show (j : ℝ) + p = ((j : ℝ) + 1) - q by ring,
      show ((j : ℝ) + 1) ^ 2 - p ^ 2 = (((j : ℝ) + 1) - p) * (((j : ℝ) + 1) + p) by ring,
      show ((j : ℝ) + 1) ^ 2 - q ^ 2 = (((j : ℝ) + 1) - q) * (((j : ℝ) + 1) + q) by ring]
    exact term_identity _ p q (by positivity) (by linarith) (by linarith) (by rw [hq]; linarith)
      (by linarith) hqp
  have hZ := hasSum_inv_succ_sq
  have hsum : HasSum (fun j : ℕ => X p (2 * j) ^ 2 / 4 + X p (2 * j + 1) ^ 2 / 4)
      (((p * q) ^ 2 / 4) * (8 * (π ^ 2 / 6) + (π ^ 2 / Real.sin (π * p) ^ 2 - 1 / p ^ 2) +
        (π ^ 2 / Real.sin (π * q) ^ 2 - 1 / q ^ 2) + c1 * ((1 / p - π * Real.cot (π * p)) / p) +
        c2 * ((1 / q - π * Real.cot (π * q)) / q))) := by
    rw [funext term]
    exact ((((hZ.mul_left 8).add (hasSum_T hp0 hp1)).add (hasSum_T hq0 hq1)).add
      ((hasSum_K hp0 hp1).mul_left c1) |>.add ((hasSum_K hq0 hq1).mul_left c2)).mul_left _
  have hge : Summable fun j : ℕ => X p (2 * j) ^ 2 / 4 :=
    Summable.of_nonneg_of_le (fun j => by positivity)
      (fun j => le_add_of_nonneg_right (by positivity)) hsum.summable
  have hho : Summable fun j : ℕ => X p (2 * j + 1) ^ 2 / 4 :=
    Summable.of_nonneg_of_le (fun j => by positivity)
      (fun j => le_add_of_nonneg_left (by positivity)) hsum.summable
  have hall := HasSum.even_add_odd (f := fun k => X p k ^ 2 / 4) hge.hasSum hho.hasSum
  rw [(hge.hasSum.add hho.hasSum).unique hsum] at hall
  refine (show _ = density p from ?_) ▸ hall
  have hsq : Real.sin (π * q) = Real.sin (π * p) := by
    rw [hq, show π * (1 - p) = π - π * p by ring, Real.sin_pi_sub]
  have hcq : Real.cos (π * q) = -Real.cos (π * p) := by
    rw [hq, show π * (1 - p) = π - π * p by ring, Real.cos_pi_sub]
  have hs := (sin_pos_of_unit hp0 hp1).ne'
  have h12 : 1 - 2 * p ≠ 0 := by intro h; apply hp; linarith
  have hv := value_eq p (Real.sin (π * p)) (Real.cos (π * p)) π hp0.ne' (by linarith) hs h12
  simp only [density, c1, c2, Real.cot_eq_cos_div_sin, hsq, hcq]
  rw [hq]
  linear_combination hv

/-- **The fair case** (Defant and Kravitz, Theorem 6.2): at `p = 1/2` the density is `(π² - 9)/12`. -/
theorem hasSum_density_half : HasSum (fun k => X (1 / 2) k ^ 2 / 4) ((π ^ 2 - 9) / 12) := by
  have hp0 : (0 : ℝ) < 1 / 2 := by norm_num
  have hp1 : (1 : ℝ) / 2 < 1 := by norm_num
  let T : ℕ → ℝ := fun n => 1 / (((n : ℝ) + 1) + 1 / 2) ^ 2 + 1 / (((n : ℝ) + 1) - 1 / 2) ^ 2
  let K : ℕ → ℝ := fun n => 2 / (((n : ℝ) + 1) ^ 2 - (1 / 2) ^ 2)
  have term : ∀ j : ℕ, X (1 / 2) (2 * j) ^ 2 / 4 + X (1 / 2) (2 * j + 1) ^ 2 / 4 =
      (1 / 64) * (8 * (1 / ((j : ℝ) + 1) ^ 2) + 4 * T j - 8 * K j) := by
    intro j
    have hj := j.cast_nonneg (α := ℝ)
    rw [X_even hp0 hp1, X_odd hp0 hp1]
    simp only [T, K]
    rw [show (j : ℝ) + (1 - 1 / 2) = ((j : ℝ) + 1) - 1 / 2 by ring,
      show (j : ℝ) + 1 / 2 = ((j : ℝ) + 1) - 1 / 2 by ring,
      show ((j : ℝ) + 1) ^ 2 - (1 / 2) ^ 2 = (((j : ℝ) + 1) - 1 / 2) * (((j : ℝ) + 1) + 1 / 2) by ring,
      show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num, show (1 : ℝ) / 2 * (1 / 2) = 1 / 4 by norm_num]
    exact term_identity_half _ (by positivity) (by linarith) (by linarith)
  have hsum : HasSum (fun j : ℕ => X (1 / 2) (2 * j) ^ 2 / 4 + X (1 / 2) (2 * j + 1) ^ 2 / 4)
      ((1 / 64) * (8 * (π ^ 2 / 6) + 4 * (π ^ 2 / Real.sin (π * (1 / 2)) ^ 2 - 1 / (1 / 2) ^ 2) -
        8 * ((1 / (1 / 2) - π * Real.cot (π * (1 / 2))) / (1 / 2)))) := by
    rw [funext term]
    exact (((hasSum_inv_succ_sq.mul_left 8).add ((hasSum_T hp0 hp1).mul_left 4)).sub
      ((hasSum_K hp0 hp1).mul_left 8)).mul_left _
  have hge : Summable fun j : ℕ => X (1 / 2) (2 * j) ^ 2 / 4 :=
    Summable.of_nonneg_of_le (fun j => by positivity)
      (fun j => le_add_of_nonneg_right (by positivity)) hsum.summable
  have hho : Summable fun j : ℕ => X (1 / 2) (2 * j + 1) ^ 2 / 4 :=
    Summable.of_nonneg_of_le (fun j => by positivity)
      (fun j => le_add_of_nonneg_left (by positivity)) hsum.summable
  have hall := HasSum.even_add_odd (f := fun k => X (1 / 2) k ^ 2 / 4) hge.hasSum hho.hasSum
  rw [(hge.hasSum.add hho.hasSum).unique hsum] at hall
  refine (show _ = (π ^ 2 - 9) / 12 from ?_) ▸ hall
  rw [show π * (1 / 2) = π / 2 by ring, Real.sin_pi_div_two, Real.cot_eq_cos_div_sin, Real.cos_pi_div_two]
  ring

end HitomezashiBiased
