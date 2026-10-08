import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Theorem 8, segment optima: the three computations

When `K` has a pair of parallel sides `k, k̄`, an optimum of the limit LP can be a segment, fixed by
two tight points `s₁ < s₂` on side `k` and one point `s₃` on `k̄`. The proof of Theorem 8 uses three
facts, proved here.

* `kkt_segment_iff`: positive multipliers with `μ₁ + μ₂ = μ₃`, `(μ₁ + μ₂) w = 1` and
  `μ₁ s₁ + μ₂ s₂ + μ₃ s₃ = 0` exist iff `s₁ < -s₃ < s₂`.
* `sigma_inner`: `∫∫_{a < s₁ < x < s₂ < b} (s₂ - s₁) = ½ (x - a)(b - x)(b - a)`.
* `segment_prob`: if `F G` is constant on `[α, β]` and `F' = S F`, then
  `F(α) G(α) + ∫_α^β G F' = F G · (1 + S (β - α))`.
-/

namespace Enclosing

open intervalIntegral

/-- Integral of an affine function. -/
lemma integral_affine (a b c d : ℝ) :
    ∫ s in a..b, (c - d * s) = c * (b - a) - d * (b ^ 2 - a ^ 2) / 2 := by
  rw [integral_sub (f := fun _ => c) (g := fun s => d * s) intervalIntegrable_const
    ((by fun_prop : Continuous fun s : ℝ => d * s).intervalIntegrable a b), integral_const_mul]
  simp [integral_id]
  ring

/-- KKT condition of a segment optimum. -/
theorem kkt_segment_iff {s₁ s₂ s₃ w : ℝ} (h12 : s₁ < s₂) (hw : 0 < w) :
    (∃ μ₁ μ₂ μ₃ : ℝ, 0 < μ₁ ∧ 0 < μ₂ ∧ 0 < μ₃ ∧ μ₁ + μ₂ = μ₃ ∧ (μ₁ + μ₂) * w = 1 ∧
        μ₁ * s₁ + μ₂ * s₂ + μ₃ * s₃ = 0) ↔ s₁ < -s₃ ∧ -s₃ < s₂ := by
  constructor
  · rintro ⟨μ₁, μ₂, μ₃, h1, h2, -, rfl, -, hs⟩
    constructor <;> nlinarith
  · rintro ⟨hl, hr⟩
    -- `-s₃ = (μ₁ s₁ + μ₂ s₂) / (μ₁ + μ₂)` with weights proportional to the distances
    have hd : 0 < s₂ - s₁ := by linarith
    refine ⟨(s₂ + s₃) / ((s₂ - s₁) * w), (-s₃ - s₁) / ((s₂ - s₁) * w), 1 / w,
      by apply div_pos <;> nlinarith, by apply div_pos <;> nlinarith, by positivity, ?_, ?_, ?_⟩
    · field_simp; ring
    · field_simp; ring
    · field_simp; ring

/-- The inner integral defining `σ_k`: pairs `s₁ < x < s₂` on a side `[a, b]`, weighted by the
Jacobian `s₂ - s₁`. -/
theorem sigma_inner (a b x : ℝ) :
    ∫ s₁ in a..x, ∫ s₂ in x..b, (s₂ - s₁) = (1 / 2) * (x - a) * (b - x) * (b - a) := by
  have inner : ∀ s₁ : ℝ, ∫ s₂ in x..b, (s₂ - s₁) = (b ^ 2 - x ^ 2) / 2 - (b - x) * s₁ := by
    intro s₁
    rw [integral_sub intervalIntegrable_id intervalIntegrable_const]
    simp [integral_id]
  simp_rw [inner, integral_affine]
  ring

/-- `σ_k` for a side `[-1, 1]` facing a parallel side with the same projection (regular polygons
in the normalisation of Section 7): `∫_{-1}^{1} ½ (s+1)(1-s)·2 ds = 4/3`. -/
theorem sigma_regular :
    ∫ x in (-1 : ℝ)..1, ∫ s₁ in (-1 : ℝ)..x, ∫ s₂ in x..1, (s₂ - s₁) = 4 / 3 := by
  simp_rw [sigma_inner]
  have : (fun x : ℝ => 1 / 2 * (x - -1) * (1 - x) * (1 - -1)) = fun x => 1 - x ^ 2 := by
    funext x; ring
  rw [this, integral_sub (f := fun _ => (1 : ℝ)) (g := fun x => x ^ 2) intervalIntegrable_const
    ((continuous_pow 2).intervalIntegrable _ _)]
  simp [integral_pow]
  norm_num

/-- The segment-case probability. `F` is the distribution function of the largest lower bound `ℓ`
and `G` the survival function of the smallest upper bound `r` on the chord `[α, β]`. If `F G` is
the constant `K₀` there and `F' = S F`, then `F(α) G(α) + ∫_α^β G dF = K₀ (1 + S (β - α))`. -/
theorem segment_prob {F G : ℝ → ℝ} {α β S K₀ : ℝ}
    (hF : ∀ y ∈ Set.uIcc α β, HasDerivAt F (S * F y) y)
    (hFG : ∀ y ∈ Set.uIcc α β, F y * G y = K₀) :
    F α * G α + ∫ y in α..β, G y * deriv F y = K₀ * (1 + S * (β - α)) := by
  have hα : α ∈ Set.uIcc α β := Set.left_mem_uIcc
  have : Set.EqOn (fun y => G y * deriv F y) (fun _ => S * K₀) (Set.uIcc α β) := by
    intro y hy
    simp only
    rw [(hF y hy).deriv, ← hFG y hy]
    ring
  rw [integral_congr this, hFG α hα]
  simp
  ring

/-- **The cone condition is "the origin is inside the tetrahedron"** (Theorem 8, remark after the
definition of `T_nd`). Rows `(hᵣ, xᵣ, yᵣ, zᵣ)` with `hᵣ > 0` (here `(x, y) = u` and `z = -s`):
`e₁` is a positive combination of the rows iff the origin is a combination of the points
`(xᵣ, yᵣ, zᵣ)/hᵣ` with positive barycentric weights. -/
theorem kkt_iff_origin_inside {k : ℕ} (h x y z : Fin k → ℝ) (hh : ∀ r, 0 < h r) :
    (∃ l : Fin k → ℝ, (∀ r, 0 < l r) ∧ ∑ r, l r * h r = 1 ∧ ∑ r, l r * x r = 0 ∧
        ∑ r, l r * y r = 0 ∧ ∑ r, l r * z r = 0) ↔
      (∃ w : Fin k → ℝ, (∀ r, 0 < w r) ∧ ∑ r, w r = 1 ∧ ∑ r, w r * (x r / h r) = 0 ∧
        ∑ r, w r * (y r / h r) = 0 ∧ ∑ r, w r * (z r / h r) = 0) := by
  have key : ∀ (l v : Fin k → ℝ) r, l r * h r * (v r / h r) = l r * v r := fun l v r => by
    have := (hh r).ne'; field_simp
  constructor
  · rintro ⟨l, hl, h1, hx, hy, hz⟩
    refine ⟨fun r => l r * h r, fun r => mul_pos (hl r) (hh r), h1, ?_, ?_, ?_⟩ <;>
      simp only [key] <;> assumption
  · rintro ⟨w, hw, h1, hx, hy, hz⟩
    refine ⟨fun r => w r / h r, fun r => div_pos (hw r) (hh r), ?_, ?_, ?_, ?_⟩
    · rw [← h1]; exact Finset.sum_congr rfl fun r _ => by have := (hh r).ne'; field_simp
    · rw [← hx]; exact Finset.sum_congr rfl fun r _ => by ring
    · rw [← hy]; exact Finset.sum_congr rfl fun r _ => by ring
    · rw [← hz]; exact Finset.sum_congr rfl fun r _ => by ring

end Enclosing
