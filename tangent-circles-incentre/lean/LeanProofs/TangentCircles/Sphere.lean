import LeanProofs.TangentCircles.Integral

/-!
# Tangent circles: the uniform sphere (Section 5)

With `d = p - q`, `ω = d + η` and `u = arcsin (sin η / cos s)`, the probability element of the four
endpoint branches of a line is `K (cos ω / √(cos² s - sin² η)) dz dη`, which in `(z, u)` becomes
`K (cos ω / cos η) dz du = K (cos d - sin d tan η) dz du` (`fold_element`).
The lines at `η` and `-η`
give the same `|u|`, and their elements add to `2 K cos d dz d|u|` (`fold_pair`), with no `η` left.
The lune: the side misses `I` exactly when `L = 2s > 2α + 2β = π - 2γ`, a lune of width `2γ = C`
(`lune`), whose area is the fraction `C / (2π)` of the sphere.
-/

open Real

namespace TangentCircles

lemma fold_element {d η : ℝ} (hη : Real.cos η ≠ 0) :
    Real.cos (d + η) / Real.cos η = Real.cos d - Real.sin d * Real.tan η := by
  rw [Real.cos_add, Real.tan_eq_sin_div_cos]
  field_simp

lemma fold_pair {d η : ℝ} (hη : Real.cos η ≠ 0) :
    Real.cos (d + η) / Real.cos η + Real.cos (d + -η) / Real.cos (-η) = 2 * Real.cos d := by
  rw [fold_element hη, fold_element (by rwa [Real.cos_neg]), Real.tan_neg]
  ring

/-- Chain rule for the substitution: `g s η = du/dη`, so
`cos ω / √(cos² s - sin² η) = (cos ω / cos η) g`. -/
lemma element_change {s η ω : ℝ} (hη : Real.cos η ≠ 0) :
    Real.cos ω / Real.sqrt (Real.cos s ^ 2 - Real.sin η ^ 2) =
      (Real.cos ω / Real.cos η) * g s η := by
  unfold g
  field_simp

/-- The miss event as a lune: with `α + β + γ = π/2`, `s > α + β` iff `2s > π - 2γ`. -/
lemma lune {s α β γ : ℝ} (h : α + β + γ = π / 2) : α + β < s ↔ π - 2 * γ < 2 * s := by
  constructor <;> intro hs <;> linarith

/-- The lune `L ∈ (π - C, π]` occupies the fraction `C / (2π)` of the longitudes `(-π, π]`. -/
lemma lune_fraction {C : ℝ} : (π - (π - C)) / (2 * π) = C / (2 * π) := by ring

end TangentCircles
