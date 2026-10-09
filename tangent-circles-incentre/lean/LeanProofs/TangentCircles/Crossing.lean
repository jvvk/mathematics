import LeanProofs.TangentCircles.Chords
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Tangent circles: the crossing law (Lemma 2)

The crossing height `z` has density `f(z) = (1/π) (a/(a² + z²) + b/(b² + z²))` on `|z| < √(ab)`.
* `cdf`: `∫₀ʳ f = (arctan (r/a) + arctan (r/b)) / π`, i.e. `(p + q)/π` where `tan p = r/a`,
  `tan q = r/b`;
* `half_mass`: `arctan (√(ab)/a) + arctan (√(ab)/b) = π/2`, so each sign of `z` has
  probability `1/2`;
* `tail`: `∫_r^{√(ab)} f = 1/2 - (arctan (r/a) + arctan (r/b)) / π`.
In terms of the angle `θ = π - p - q` subtended by the two centres at `Z`: `θ` is uniform
on `(π/2, π)`.
-/

open Real Set intervalIntegral MeasureTheory

namespace TangentCircles

/-- The crossing density on `z ≥ 0` (the law is symmetric in `z`). -/
noncomputable def f (a b z : ℝ) : ℝ := (1 / π) * (a / (a ^ 2 + z ^ 2) + b / (b ^ 2 + z ^ 2))

/-- Its antiderivative. -/
noncomputable def F (a b z : ℝ) : ℝ := (Real.arctan (z / a) + Real.arctan (z / b)) / π

lemma hasDerivAt_arctan_div {a : ℝ} (ha : 0 < a) (z : ℝ) :
    HasDerivAt (fun z => Real.arctan (z / a)) (a / (a ^ 2 + z ^ 2)) z := by
  have h := (Real.hasDerivAt_arctan (z / a)).comp z ((hasDerivAt_id z).div_const a)
  have hfun : (fun z => Real.arctan (z / a)) = (Real.arctan ∘ fun x => id x / a) := rfl
  rw [hfun]
  convert h using 1
  field_simp

lemma hasDerivAt_F {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (z : ℝ) :
    HasDerivAt (F a b) (f a b z) z := by
  have := ((hasDerivAt_arctan_div ha z).add (hasDerivAt_arctan_div hb z)).div_const π
  show HasDerivAt (fun z => (Real.arctan (z / a) + Real.arctan (z / b)) / π) _ z
  convert this using 1
  unfold f; ring

lemma continuous_f {a b : ℝ} (ha : 0 < a) (hb : 0 < b) : Continuous (f a b) := by
  unfold f
  apply continuous_const.mul
  apply Continuous.add
  · exact continuous_const.div (by fun_prop) (fun z => by positivity)
  · exact continuous_const.div (by fun_prop) (fun z => by positivity)

/-- `∫ₓʸ f = F y - F x`. -/
theorem integral_f {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (x y : ℝ) :
    ∫ z in x..y, f a b z = F a b y - F a b x :=
  integral_eq_sub_of_hasDerivAt (fun z _ => hasDerivAt_F ha hb z)
    ((continuous_f ha hb).intervalIntegrable _ _)

/-- `P(0 < z < r) = (p + q)/π`. -/
theorem cdf {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (r : ℝ) :
    ∫ z in (0 : ℝ)..r, f a b z = (Real.arctan (r / a) + Real.arctan (r / b)) / π := by
  rw [integral_f ha hb]; unfold F; simp

/-- The two arctangents at the end of the support add up to `π/2`. -/
theorem half_mass {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Real.arctan (Real.sqrt (a * b) / a) + Real.arctan (Real.sqrt (a * b) / b) = π / 2 := by
  have hs : 0 < Real.sqrt (a * b) := Real.sqrt_pos.2 (mul_pos ha hb)
  have hx : 0 < Real.sqrt (a * b) / a := div_pos hs ha
  have hinv : Real.sqrt (a * b) / b = (Real.sqrt (a * b) / a)⁻¹ := by
    have hsq : Real.sqrt (a * b) * Real.sqrt (a * b) = a * b := Real.mul_self_sqrt (by positivity)
    field_simp
    linarith
  rw [hinv, Real.arctan_inv_of_pos hx]; ring

/-- Each sign of `z` carries probability `1/2`. -/
theorem half {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ∫ z in (0 : ℝ)..Real.sqrt (a * b), f a b z = 1 / 2 := by
  rw [cdf ha hb, half_mass ha hb]; field_simp

/-- `P(z > r) = 1/2 - (p + q)/π` for `0 ≤ r ≤ √(ab)`. -/
theorem tail {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (r : ℝ) :
    ∫ z in r..Real.sqrt (a * b), f a b z =
      1 / 2 - (Real.arctan (r / a) + Real.arctan (r / b)) / π := by
  rw [integral_f ha hb, ← cdf ha hb, ← half ha hb, cdf ha hb, cdf ha hb]; unfold F; ring

/-- The density formula from the line-integral form (the tidying step): with `z cos p = a sin p`,
`z cos q = b sin q`, `z ≠ 0` and `cos p, cos q > 0`,
`(a + b) cos p cos q cos (p - q) / (a b) = a/(a² + z²) + b/(b² + z²)`. -/
theorem density_form {a b z p q : ℝ} (ha : 0 < a) (hb : 0 < b) (hp : 0 < Real.cos p)
    (hq : 0 < Real.cos q) (hzp : z * Real.cos p = a * Real.sin p)
    (hzq : z * Real.cos q = b * Real.sin q) :
    (a + b) * Real.cos p * Real.cos q * Real.cos (p - q) / (a * b) =
      a / (a ^ 2 + z ^ 2) + b / (b ^ 2 + z ^ 2) := by
  have h : a * Real.sin p * Real.cos q = b * Real.sin q * Real.cos p := by
    calc a * Real.sin p * Real.cos q = (z * Real.cos p) * Real.cos q := by rw [hzp]
      _ = (z * Real.cos q) * Real.cos p := by ring
      _ = b * Real.sin q * Real.cos p := by rw [hzq]
  rw [tidy h, a_div ha.ne' hp.ne' hzp, a_div hb.ne' hq.ne' hzq]
  field_simp

end TangentCircles
