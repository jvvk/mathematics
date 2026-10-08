import EnclosingCopy.Enclosing.Segment
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Section 7: regular polygons, the scale-and-tilt integrals and the segment term `8/(3q²)`

Normalise the regular `q`-gon to inradius 1 and rescale positions so that every side is
`s ∈ [-1, 1]` (so `Lᵢ = 2`, `hᵢ = 1`). Then `R(t, Θ) = (t - |Θ|) P`, the void probability is
`exp (2 q ε)` and the weight `e^{-2t}` of `V(K)` becomes `e^{-2qt}`. The integrals that remain are

* `scale_tilt k`: `∫_ℝ ∫_{t > |Θ|} e^{-2qt} (t - |Θ|)^k dt dΘ = k! / (q (2q)^(k+1))`;
  `k = 2` gives the area factor `1/(4q⁴)` and `k = 1` the width factor `1/(4q³)`;
* `sum_sin_eq_cot`: for `q = 2r`, `∑_{j=1}^{r-1} sin (2πj/q) = cot (π/q)`, hence `S_k = 2 cot (π/q)`;
* `segment_term_regular`: the segment term of Theorem 8 equals `8 / (3 q²)`.
-/

namespace Enclosing

open MeasureTheory Set Real

/-- `∫_{u > 0} u^k e^{-c u} du = k! / c^(k+1)`. -/
lemma integral_pow_mul_exp_neg (k : ℕ) {c : ℝ} (hc : 0 < c) :
    ∫ u in Ioi (0 : ℝ), u ^ k * exp (-(c * u)) = k.factorial / c ^ (k + 1) := by
  have h := integral_rpow_mul_exp_neg_mul_Ioi (a := (k : ℝ) + 1) (by positivity) hc
  rw [Gamma_nat_eq_factorial, add_sub_cancel_right] at h
  have hcongr : ∫ u in Ioi (0 : ℝ), u ^ k * exp (-(c * u))
      = ∫ u in Ioi (0 : ℝ), u ^ ((k : ℝ)) * exp (-(c * u)) :=
    setIntegral_congr_fun measurableSet_Ioi fun u _ => by simp [Real.rpow_natCast]
  rw [hcongr, h, one_div, Real.inv_rpow hc.le, ← Real.rpow_natCast c (k + 1)]
  push_cast
  ring

/-- Translation on a half-line: `∫_{t > c} f t = ∫_{u > 0} f (u + c)`. -/
lemma setIntegral_Ioi_shift (f : ℝ → ℝ) (c : ℝ) :
    ∫ t in Ioi c, f t = ∫ u in Ioi (0 : ℝ), f (u + c) := by
  rw [← integral_indicator measurableSet_Ioi, ← integral_indicator measurableSet_Ioi,
    ← integral_add_right_eq_self _ c]
  congr 1
  funext u
  by_cases hu : 0 < u
  · rw [indicator_of_mem (show u + c ∈ Ioi c by simp [hu]), indicator_of_mem (show u ∈ Ioi 0 from hu)]
  · rw [indicator_of_notMem (show u + c ∉ Ioi c by simpa using hu),
      indicator_of_notMem (show u ∉ Ioi (0 : ℝ) from hu)]

/-- The inner (scale) integral: `∫_{t > |Θ|} e^{-ct} (t - |Θ|)^k dt = e^{-c|Θ|} k!/c^(k+1)`. -/
lemma inner_scale (k : ℕ) {c : ℝ} (hc : 0 < c) (Θ : ℝ) :
    ∫ t in Ioi |Θ|, exp (-(c * t)) * (t - |Θ|) ^ k
      = exp (-(c * |Θ|)) * (k.factorial / c ^ (k + 1)) := by
  rw [setIntegral_Ioi_shift, ← integral_pow_mul_exp_neg k hc, ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
  simp only [add_sub_cancel_right]
  rw [show -(c * (u + |Θ|)) = -(c * |Θ|) + -(c * u) by ring, exp_add]
  ring

/-- `∫_ℝ e^{-c|Θ|} dΘ = 2/c`. -/
lemma integral_exp_neg_abs {c : ℝ} (hc : 0 < c) : ∫ Θ, exp (-(c * |Θ|)) = 2 / c := by
  rw [integral_comp_abs (f := fun x => exp (-(c * x)))]
  have := integral_exp_mul_Ioi (a := -c) (by linarith) 0
  simp only [mul_zero, exp_zero, neg_mul] at this
  rw [this]
  field_simp

/-- **The scale-and-tilt integral** of Section 7. -/
theorem scale_tilt (k : ℕ) {q : ℝ} (hq : 0 < q) :
    ∫ Θ, ∫ t in Ioi |Θ|, exp (-(2 * q * t)) * (t - |Θ|) ^ k
      = k.factorial / (q * (2 * q) ^ (k + 1)) := by
  have hc : 0 < 2 * q := by linarith
  simp_rw [inner_scale k hc]
  rw [integral_mul_const, integral_exp_neg_abs hc]
  field_simp

/-- The area factor of `V(K)`: `∫∫ e^{-2qt} (t - |Θ|)² = 1/(4 q⁴)`. -/
theorem scale_tilt_area {q : ℝ} (hq : 0 < q) :
    ∫ Θ, ∫ t in Ioi |Θ|, exp (-(2 * q * t)) * (t - |Θ|) ^ 2 = 1 / (4 * q ^ 4) := by
  rw [scale_tilt 2 hq]
  norm_num [Nat.factorial]
  ring

/-- The width factor: `∫∫ e^{-2qt} (t - |Θ|) = 1/(4 q³)`. -/
theorem scale_tilt_width {q : ℝ} (hq : 0 < q) :
    ∫ Θ, ∫ t in Ioi |Θ|, exp (-(2 * q * t)) * (t - |Θ|) ^ 1 = 1 / (4 * q ^ 3) := by
  rw [scale_tilt 1 hq]
  norm_num [Nat.factorial]
  ring

/-- Telescoping product-to-sum: `2 sin(x/2) sin(jx) = cos((j-½)x) - cos((j+½)x)`. -/
lemma two_sin_mul_sin (x : ℝ) (j : ℝ) :
    2 * sin (x / 2) * sin (j * x) = cos ((j - 1 / 2) * x) - cos ((j + 1 / 2) * x) := by
  rw [show (j - 1 / 2) * x = j * x - x / 2 by ring, show (j + 1 / 2) * x = j * x + x / 2 by ring,
    cos_sub, cos_add]
  ring

/-- `∑_{j=1}^{r-1} sin (π j / r) = cot (π / (2r))`. -/
theorem sum_sin_eq_cot {r : ℕ} (hr : 1 ≤ r) :
    ∑ j ∈ Finset.Ico 1 r, sin (π * j / r) = cos (π / (2 * r)) / sin (π / (2 * r)) := by
  have hrpos : (0 : ℝ) < r := by exact_mod_cast hr
  have hs : 0 < sin (π / (2 * r)) := by
    apply sin_pos_of_pos_of_lt_pi (by positivity)
    rw [div_lt_iff₀ (by positivity)]
    nlinarith [pi_pos, (show (1 : ℝ) ≤ r by exact_mod_cast hr)]
  rw [eq_div_iff hs.ne']
  set x := π / r with hx
  have hx2 : π / (2 * r) = x / 2 := by rw [hx]; field_simp
  -- telescoping sum `∑_{j=1}^{n-1} (cos((j-½)x) - cos((j+½)x)) = cos(x/2) - cos((n-½)x)`
  have tel : ∀ n : ℕ, 1 ≤ n → ∑ j ∈ Finset.Ico 1 n, 2 * sin (x / 2) * sin (j * x)
      = cos (x / 2) - cos ((n - 1 / 2) * x) := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => simp; ring_nf
    | succ n hn ih =>
      rw [Finset.sum_Ico_succ_top hn, ih, two_sin_mul_sin]
      push_cast
      ring_nf
  have key := tel r hr
  have hend : cos ((r - 1 / 2) * x) = -cos (x / 2) := by
    rw [show ((r : ℝ) - 1 / 2) * x = π - x / 2 by rw [hx]; field_simp, cos_pi_sub]
  rw [hend, ← Finset.mul_sum] at key
  have : ∀ j : ℕ, π * j / r = j * x := fun j => by rw [hx]; ring
  simp_rw [this, hx2]
  nlinarith [key]

/-- `S_k` for the regular `q`-gon, `q = 2r`, in the side normalisation `L = 2`:
`S_k = ∑_{j=1}^{r-1} 2 sin (2πj/q) = 2 cot (π/q)`. -/
theorem S_regular {r : ℕ} (hr : 1 ≤ r) :
    ∑ j ∈ Finset.Ico 1 r, 2 * sin (2 * π * j / (2 * r)) = 2 * (cos (π / (2 * r)) / sin (π / (2 * r))) := by
  rw [← Finset.mul_sum, ← sum_sin_eq_cot hr]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  have : (0 : ℝ) < r := by exact_mod_cast hr
  field_simp

/-- **The segment term for the regular `q`-gon** (`q = 2r` even). Theorem 8's sum over the `q`
ordered pairs of parallel sides, each contributing
`σ_k ∫∫ e^{-2qt} w_k [width R + S_k area R]`, with `σ_k = 4/3` (`sigma_regular`), `w_k = 2`,
`width R = 2 (t - |Θ|)`, `area R = (q tan(π/q)) (t - |Θ|)²` and `S_k = 2 cot(π/q)`, is `8/(3q²)`. -/
theorem segment_term_regular {r : ℕ} (hr : 2 ≤ r) :
    let q : ℝ := 2 * r
    let S : ℝ := ∑ j ∈ Finset.Ico 1 r, 2 * sin (2 * π * j / q)
    let areaP : ℝ := q * tan (π / q)
    q * (∫ x in (-1 : ℝ)..1, ∫ s₁ in (-1 : ℝ)..x, ∫ s₂ in x..1, (s₂ - s₁)) *
        (2 * (2 * ∫ Θ, ∫ t in Ioi |Θ|, exp (-(2 * q * t)) * (t - |Θ|) ^ 1)
          + 2 * S * areaP * ∫ Θ, ∫ t in Ioi |Θ|, exp (-(2 * q * t)) * (t - |Θ|) ^ 2)
      = 8 / (3 * q ^ 2) := by
  intro q S areaP
  have hr1 : 1 ≤ r := by omega
  have hq : 0 < q := by positivity
  have hS : S = 2 * (cos (π / q) / sin (π / q)) := by
    simp only [S, q]; exact S_regular hr1
  have h4 : (4 : ℝ) ≤ q := by
    have : (2 : ℝ) ≤ r := by exact_mod_cast hr
    simp only [q]; linarith
  have hsin : 0 < sin (π / q) := by
    apply sin_pos_of_pos_of_lt_pi (by positivity)
    rw [div_lt_iff₀ hq]
    nlinarith [pi_pos]
  have hcos : 0 < cos (π / q) := by
    apply cos_pos_of_mem_Ioo
    constructor
    · have : 0 < π / q := by positivity
      linarith [pi_pos]
    · rw [div_lt_div_iff₀ hq (by norm_num)]
      nlinarith [pi_pos]
  rw [sigma_regular, scale_tilt_width hq, scale_tilt_area hq, hS]
  simp only [areaP, tan_eq_sin_div_cos]
  field_simp
  ring

end Enclosing
