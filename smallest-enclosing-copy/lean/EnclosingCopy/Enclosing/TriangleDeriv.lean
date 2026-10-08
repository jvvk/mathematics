import EnclosingCopy.Enclosing.Triangle
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Section 6: from the limit model to Corollary 2

For a triangle, the paper reduces `p` to `p = 2 ∑ₖ Iₖ / (Q L₁ L₂ L₃)` with `Q = ½ ∑ Lᵢ²`, where

* the integral over the tilt `Θ > 0` and the heights `Hᵢ ≤ Θ aᵢ`, weighted by the void probability
  `exp (∑ Lᵢ Hᵢ)` of Lemma 7, is `1/(Q L₁ L₂ L₃)` (`theta_height`; it uses `∑ Lᵢ aᵢ = -Q`, identity
  (1c));
* `Iₖ = (Lₖ/2) ∫∫ ((x - aₖ)(bₖ - x))₊ dsᵢ dsⱼ` with `x = -(Lᵢ sᵢ + Lⱼ sⱼ)/Lₖ` is
  `L₁ L₂ L₃ Lₖ² g(Lᵢ²/Lₖ², Lⱼ²/Lₖ²) / 8` (`Ik_eq`; sides are written by midpoint `m` and length
  `L`, and `∑ Lᵢ mᵢ = 0` is identity (1c) again);
* the two combine to the formula of Corollary 2 (`p_from_Ik`).
-/

namespace Enclosing

open MeasureTheory Set Real intervalIntegral

/-- `∫_{H < c} e^{L H} dH = e^{L c} / L`. -/
lemma integral_exp_Iic {L : ℝ} (hL : 0 < L) (c : ℝ) :
    ∫ H in Iic c, exp (L * H) = exp (L * c) / L := integral_exp_mul_Iic hL c

/-- **The tilt-and-height integral** (one sign of `Θ`). -/
theorem theta_height {L₁ L₂ L₃ a₁ a₂ a₃ Q : ℝ} (h1 : 0 < L₁) (h2 : 0 < L₂) (h3 : 0 < L₃)
    (hQ : 0 < Q) (hsum : L₁ * a₁ + L₂ * a₂ + L₃ * a₃ = -Q) :
    ∫ Θ in Ioi (0 : ℝ), (∫ H in Iic (Θ * a₁), exp (L₁ * H)) * (∫ H in Iic (Θ * a₂), exp (L₂ * H)) *
        (∫ H in Iic (Θ * a₃), exp (L₃ * H)) = 1 / (Q * L₁ * L₂ * L₃) := by
  simp_rw [integral_exp_Iic h1, integral_exp_Iic h2, integral_exp_Iic h3]
  have : ∀ Θ : ℝ, exp (L₁ * (Θ * a₁)) / L₁ * (exp (L₂ * (Θ * a₂)) / L₂) * (exp (L₃ * (Θ * a₃)) / L₃)
      = exp (-Q * Θ) / (L₁ * L₂ * L₃) := fun Θ => by
    rw [div_mul_div_comm, div_mul_div_comm, ← exp_add, ← exp_add]
    congr 2
    linear_combination Θ * hsum
  simp_rw [this]
  rw [MeasureTheory.integral_div, integral_exp_mul_Ioi (by linarith) 0]
  simp only [mul_zero, exp_zero]
  field_simp

/-- Affine change of variables onto `[-1, 1]`: `∫_{m-L/2}^{m+L/2} f = (L/2) ∫_{-1}^{1} f(m + (L/2) u)`. -/
lemma integral_side (f : ℝ → ℝ) {L : ℝ} (hL : 0 < L) (m : ℝ) :
    ∫ s in (m - L / 2)..(m + L / 2), f s = (L / 2) * ∫ u in (-1 : ℝ)..1, f (L / 2 * u + m) := by
  rw [intervalIntegral.integral_comp_mul_add (a := -1) (b := 1) f (by positivity : L / 2 ≠ 0) m,
    smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ (by positivity : L / 2 ≠ 0), one_mul]
  congr 1 <;> ring

/-- The integrand of `Iₖ` in the coordinates `u, v ∈ [-1, 1]`. -/
lemma Ik_integrand {Li Lj Lk mi mj mk u v : ℝ} (hk : 0 < Lk)
    (hsum : Li * mi + Lj * mj + Lk * mk = 0) :
    let x := -(Li * (Li / 2 * u + mi) + Lj * (Lj / 2 * v + mj)) / Lk
    max 0 ((x - (mk - Lk / 2)) * ((mk + Lk / 2) - x))
      = Lk ^ 2 / 4 * fpos (Li ^ 2 / Lk ^ 2 * u + Lj ^ 2 / Lk ^ 2 * v) := by
  intro x
  have hx : x - mk = -(Lk / 2) * (Li ^ 2 / Lk ^ 2 * u + Lj ^ 2 / Lk ^ 2 * v) := by
    simp only [x]
    field_simp
    linear_combination (-2) * hsum
  have : (x - (mk - Lk / 2)) * ((mk + Lk / 2) - x)
      = Lk ^ 2 / 4 * (1 - (Li ^ 2 / Lk ^ 2 * u + Lj ^ 2 / Lk ^ 2 * v) ^ 2) := by
    have e : (x - (mk - Lk / 2)) * ((mk + Lk / 2) - x) = Lk ^ 2 / 4 - (x - mk) ^ 2 := by ring
    rw [e, hx]; ring
  rw [this, fpos, mul_max_of_nonneg _ _ (by positivity : (0 : ℝ) ≤ Lk ^ 2 / 4), mul_zero]

/-- **`Iₖ` in terms of `g`.** -/
theorem Ik_eq {Li Lj Lk mi mj mk : ℝ} (hi : 0 < Li) (hj : 0 < Lj) (hk : 0 < Lk)
    (hsum : Li * mi + Lj * mj + Lk * mk = 0) :
    Lk / 2 * ∫ si in (mi - Li / 2)..(mi + Li / 2), ∫ sj in (mj - Lj / 2)..(mj + Lj / 2),
        max 0 ((-(Li * si + Lj * sj) / Lk - (mk - Lk / 2)) * ((mk + Lk / 2) - -(Li * si + Lj * sj) / Lk))
      = Li * Lj * Lk * Lk ^ 2 * gfun (Li ^ 2 / Lk ^ 2) (Lj ^ 2 / Lk ^ 2) / 8 := by
  simp_rw [integral_side _ hj mj]
  rw [integral_side _ hi mi]
  simp_rw [Ik_integrand (Li := Li) (Lj := Lj) (mi := mi) (mj := mj) hk hsum]
  simp_rw [intervalIntegral.integral_const_mul]
  unfold gfun
  ring

/-- **Corollary 2 from Section 6**: `2 ∑ Iₖ / (Q L₁ L₂ L₃)`, with `Q = ½ ∑ Lᵢ²` and
`Iₖ = L₁ L₂ L₃ Lₖ² gₖ / 8`, is the triangle formula `ptri`. -/
theorem p_from_Ik {L₁ L₂ L₃ : ℝ} (h1 : 0 < L₁) (h2 : 0 < L₂) (h3 : 0 < L₃) :
    let I₁ := L₂ * L₃ * L₁ * L₁ ^ 2 * gfun (L₂ ^ 2 / L₁ ^ 2) (L₃ ^ 2 / L₁ ^ 2) / 8
    let I₂ := L₁ * L₃ * L₂ * L₂ ^ 2 * gfun (L₁ ^ 2 / L₂ ^ 2) (L₃ ^ 2 / L₂ ^ 2) / 8
    let I₃ := L₁ * L₂ * L₃ * L₃ ^ 2 * gfun (L₁ ^ 2 / L₃ ^ 2) (L₂ ^ 2 / L₃ ^ 2) / 8
    let Q := (L₁ ^ 2 + L₂ ^ 2 + L₃ ^ 2) / 2
    2 * (I₁ + I₂ + I₃) / (Q * L₁ * L₂ * L₃) = ptri (L₁ ^ 2) (L₂ ^ 2) (L₃ ^ 2) := by
  intro I₁ I₂ I₃ Q
  simp only [I₁, I₂, I₃, Q, ptri]
  field_simp
  ring

end Enclosing
