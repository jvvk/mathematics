import LeanProofs.FrankCopula.NotAffine

/-!
# The Frank conditional distribution and its integral

`C t u v = -(1/t) log(1 + (e^{-tu}-1)(e^{-tv}-1)/(e^{-t}-1))` is the Frank copula. Its `u`-derivative is the
conditional distribution function `K t u v = P(V ≤ v | U = u) = w y / (a + x y)`, with `w = e^{-tu}`,
`x = w - 1`, `y = e^{-tv} - 1`, `a = e^{-t} - 1`. Then `E[V | U = u] = 1 - ∫₀¹ K t u v dv` (layer-cake; cited, not
formalised), and the integral is computed here by the fundamental theorem of calculus, from the antiderivative
`G v = (w / x) (v - (a / (a - x)) (v + (1/t) log (a - x + x e^{-tv})))` (Mathlib's `log` is `log |·|`). Result: `1 - ∫₀¹ K = R t u`.
-/

namespace FrankCopula

open Real intervalIntegral

noncomputable def C (t u v : ℝ) : ℝ := -(1 / t) * log (1 + (exp (-t * u) - 1) * (exp (-t * v) - 1) / (exp (-t) - 1))

noncomputable def K (t u v : ℝ) : ℝ :=
  exp (-t * u) * (exp (-t * v) - 1) / ((exp (-t) - 1) + (exp (-t * u) - 1) * (exp (-t * v) - 1))

/-- The `v`-antiderivative of `K`. -/
noncomputable def G (t u v : ℝ) : ℝ :=
  exp (-t * u) / (exp (-t * u) - 1) * (v - (exp (-t) - 1) / ((exp (-t) - 1) - (exp (-t * u) - 1)) *
    (v + (1 / t) * log ((exp (-t) - 1) - (exp (-t * u) - 1) + (exp (-t * u) - 1) * exp (-t * v))))

section
variable {t u : ℝ} (ht : t ≠ 0) (hu : u ∈ Set.Ioo (0 : ℝ) 1)
include ht hu

omit hu in
/-- The common denominator `a + x y` (also the argument of the logarithm in `G`). -/
lemma den_ne (v : ℝ) (hv : v ∈ Set.Icc (0 : ℝ) 1) :
    (exp (-t) - 1) + (exp (-t * u) - 1) * (exp (-t * v) - 1) ≠ 0 := by
  have hw := exp_pos (-t * u)
  have e : (exp (-t) - 1) + (exp (-t * u) - 1) * (exp (-t * v) - 1) =
      -((exp (-t * v) - exp (-t)) + exp (-t * u) * (1 - exp (-t * v))) := by ring
  rw [e, neg_ne_zero]
  rcases lt_or_gt_of_ne ht with h | h
  · -- t < 0: 1 ≤ e^{-tv} ≤ e^{-t}
    have h1 : exp (-t * v) ≤ exp (-t) := exp_le_exp.mpr (by nlinarith [hv.2])
    have h2 : 1 ≤ exp (-t * v) := one_le_exp (by nlinarith [hv.1])
    have h3 : 1 < exp (-t) := one_lt_exp_iff.mpr (by linarith)
    rcases eq_or_lt_of_le h2 with h4 | h4
    · rw [← h4]; nlinarith
    · nlinarith [mul_pos hw (sub_pos.mpr h4)]
  · -- t > 0: e^{-t} ≤ e^{-tv} ≤ 1
    have h1 : exp (-t) ≤ exp (-t * v) := exp_le_exp.mpr (by nlinarith [hv.2])
    have h2 : exp (-t * v) ≤ 1 := exp_le_one_iff.mpr (by nlinarith [hv.1])
    have h3 : exp (-t) < 1 := exp_lt_one_iff.mpr (by linarith)
    rcases eq_or_lt_of_le h2 with h4 | h4
    · rw [h4]; nlinarith
    · nlinarith [mul_pos hw (sub_pos.mpr h4)]

lemma x_ne : exp (-t * u) - 1 ≠ 0 := by
  intro h; have := exp_eq_one_iff _ |>.mp (sub_eq_zero.mp h)
  rcases mul_eq_zero.mp this with h' | h'
  · exact ht (neg_eq_zero.mp h')
  · exact hu.1.ne' h'

lemma ax_ne : (exp (-t) - 1) - (exp (-t * u) - 1) ≠ 0 := by
  intro h
  have : -t = -t * u := exp_injective (by linarith)
  have : t * (1 - u) = 0 := by linarith
  rcases mul_eq_zero.mp this with h' | h'
  · exact ht h'
  · linarith [hu.2]

lemma hasDerivAt_G (v : ℝ) (hv : v ∈ Set.Icc (0 : ℝ) 1) : HasDerivAt (G t u) (K t u v) v := by
  have hd := den_ne (u := u) ht v hv
  have hx := x_ne ht hu
  have hax := ax_ne ht hu
  have harg : (exp (-t) - 1) - (exp (-t * u) - 1) + (exp (-t * u) - 1) * exp (-t * v) =
      (exp (-t) - 1) + (exp (-t * u) - 1) * (exp (-t * v) - 1) := by ring
  -- derivative of the log term
  have hE : HasDerivAt (fun v => exp (-t * v)) (exp (-t * v) * -t) v := by
    simpa using ((hasDerivAt_id v).const_mul (-t)).exp
  have hA : HasDerivAt (fun v => (exp (-t) - 1) - (exp (-t * u) - 1) + (exp (-t * u) - 1) * exp (-t * v))
      ((exp (-t * u) - 1) * (exp (-t * v) * -t)) v := (hE.const_mul _).const_add _
  have hL := hA.log (by rw [harg]; exact hd)
  have hB : HasDerivAt (fun v => v + (1 / t) * log ((exp (-t) - 1) - (exp (-t * u) - 1) +
      (exp (-t * u) - 1) * exp (-t * v)))
      (1 + (1 / t) * ((exp (-t * u) - 1) * (exp (-t * v) * -t) /
        ((exp (-t) - 1) - (exp (-t * u) - 1) + (exp (-t * u) - 1) * exp (-t * v)))) v :=
    (hasDerivAt_id v).add (hL.const_mul _)
  have hG := ((hasDerivAt_id v).sub (hB.const_mul ((exp (-t) - 1) /
    ((exp (-t) - 1) - (exp (-t * u) - 1))))).const_mul (exp (-t * u) / (exp (-t * u) - 1))
  refine (hG.congr_deriv ?_ : HasDerivAt (G t u) _ v)
  unfold K
  rw [harg]
  clear hG hB hL hA hE harg
  generalize exp (-t * v) = y at *
  generalize exp (-t * u) = w at *
  generalize exp (-t) = q at *
  field_simp
  ring

/-- `∫₀¹ K = 1 - R`: the conditional mean of `V` given `U = u` is `R t u`. -/
theorem integral_K : ∫ v in (0 : ℝ)..1, K t u v = 1 - R t u := by
  have hx := x_ne ht hu
  have hax := ax_ne ht hu
  rw [integral_eq_sub_of_hasDerivAt (f := G t u)]
  · have hw := exp_pos (-t * u)
    have ha : exp (-t) - 1 ≠ 0 := fun h => ht (by have := exp_eq_one_iff _ |>.mp (sub_eq_zero.mp h); linarith)
    have e1 : (exp (-t) - 1) - (exp (-t * u) - 1) + (exp (-t * u) - 1) * exp (-t * 1) =
        exp (-t * u) * (exp (-t) - 1) := by rw [mul_one]; ring
    have e0 : (exp (-t) - 1) - (exp (-t * u) - 1) + (exp (-t * u) - 1) * exp (-t * 0) = exp (-t) - 1 := by
      rw [mul_zero, exp_zero]; ring
    unfold G R
    rw [e1, e0, log_mul hw.ne' ha, log_exp]
    generalize exp (-t * u) = w at *
    generalize exp (-t) = q at *
    have hwq : w - q ≠ 0 := fun h => hax (by linarith)
    field_simp
    ring
  · intro v hv
    rw [Set.uIcc_of_le zero_le_one] at hv
    exact hasDerivAt_G ht hu v hv
  · apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le zero_le_one]
    intro v hv
    apply ContinuousAt.continuousWithinAt
    have := den_ne (u := u) ht v hv
    unfold K
    fun_prop (disch := assumption)

omit hu in
/-- **`K` is the `u`-derivative of the copula**: `∂C/∂u = K`, the conditional distribution function. -/
theorem hasDerivAt_C (v : ℝ) (hv : v ∈ Set.Icc (0 : ℝ) 1) (u' : ℝ) :
    HasDerivAt (fun u => C t u v) (K t u' v) u' := by
  have hd := den_ne (u := u') ht v hv
  have ha : exp (-t) - 1 ≠ 0 := fun h => ht (by have := exp_eq_one_iff _ |>.mp (sub_eq_zero.mp h); linarith)
  have hE : HasDerivAt (fun u => exp (-t * u)) (exp (-t * u') * -t) u' := by
    simpa using ((hasDerivAt_id u').const_mul (-t)).exp
  have hA : HasDerivAt (fun u => 1 + (exp (-t * u) - 1) * (exp (-t * v) - 1) / (exp (-t) - 1))
      (exp (-t * u') * -t * (exp (-t * v) - 1) / (exp (-t) - 1)) u' := by
    have := ((hE.sub_const 1).mul_const (exp (-t * v) - 1)).div_const (exp (-t) - 1)
    simpa using this.const_add 1
  have hne : 1 + (exp (-t * u') - 1) * (exp (-t * v) - 1) / (exp (-t) - 1) ≠ 0 := by
    rw [one_add_div ha]; exact div_ne_zero hd ha
  refine ((hA.log hne).const_mul (-(1 / t))).congr_deriv ?_
  unfold K
  rw [one_add_div ha] at *
  generalize exp (-t * v) = y at *
  generalize exp (-t * u') = w at *
  generalize exp (-t) = q at *
  field_simp

end

end FrankCopula
