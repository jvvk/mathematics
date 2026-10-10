import Mathlib

/-!
# Raising the apex raises the Gaussian centroid (MO 499635)

A convex base `K` in a hyperplane, a foot `D ∈ K`, apex `D + hν` on the normal. The height `y` of a Gaussian point of
the pyramid has density `w(y) F(1 - y/h)` on `(0, h)`, where `F(s)` is the Gaussian mass of the section
`D + s(K - D)` (quoted: the factorisation of the Gaussian and Fubini). This file proves the steps of the argument:

* `dilate_combo`: `(1-λ)(D + s₁(K-D)) + λ(D + s₂(K-D)) ⊆ D + ((1-λ)s₁ + λs₂)(K-D)`, which with the log-concavity
  of Gaussian measure (Prékopa, quoted) makes `log F` concave.
* `increment_gt`: for `φ` concave and strictly increasing, a longer interval placed lower gains more than a shorter
  interval placed higher.
* `ratio_strictMono`: hence `y ↦ φ(1 - y/h₂) - φ(1 - y/h₁)` is strictly increasing on `(0, h₁)` for `h₁ < h₂`:
  the likelihood ratio of the two height laws increases.
* `chebyshev`, `chebyshev_strict`: Chebyshev's integral inequality for similarly ordered functions, with its strict
  form; applied to `y` and the likelihood ratio it raises the conditional mean.
* `mean_mix`: adding mass above `h₁` raises the mean further.
-/

namespace GaussianApex

open Set MeasureTheory

/-! ### Sections of a cone -/

/-- Convex combinations of two dilates of a convex set about one of its points lie in the dilate with the combined
scale. -/
theorem dilate_combo {E : Type*} [AddCommGroup E] [Module ℝ E] {K : Set E} (hK : Convex ℝ K) {D : E}
    {s₁ s₂ l : ℝ} (h₁ : 0 < s₁) (h₂ : 0 < s₂) (hl0 : 0 ≤ l) (hl1 : l ≤ 1) {z₁ z₂ : E} (hz₁ : z₁ ∈ K)
    (hz₂ : z₂ ∈ K) :
    ∃ z ∈ K, (1 - l) • (D + s₁ • (z₁ - D)) + l • (D + s₂ • (z₂ - D)) = D + ((1 - l) * s₁ + l * s₂) • (z - D) := by
  set s := (1 - l) * s₁ + l * s₂ with hs
  have hs0 : 0 < s := by
    rcases lt_or_eq_of_le hl1 with h | h
    · have := mul_pos (sub_pos.mpr h) h₁; nlinarith [mul_nonneg hl0 h₂.le]
    · rw [hs, h]; simpa using h₂
  set a := (1 - l) * s₁ / s
  set b := l * s₂ / s
  have ha : 0 ≤ a := div_nonneg (mul_nonneg (by linarith) h₁.le) hs0.le
  have hb : 0 ≤ b := div_nonneg (mul_nonneg hl0 h₂.le) hs0.le
  have hab : a + b = 1 := by
    simp only [a, b]; rw [← add_div, div_eq_one_iff_eq hs0.ne']
  refine ⟨a • z₁ + b • z₂, hK hz₁ hz₂ ha hb hab, ?_⟩
  have e1 : s * a = (1 - l) * s₁ := by simp only [a]; field_simp
  have e2 : s * b = l * s₂ := by simp only [b]; field_simp
  have key : a • z₁ + b • z₂ - D = a • (z₁ - D) + b • (z₂ - D) := by
    have : a • (z₁ - D) + b • (z₂ - D) = a • z₁ + b • z₂ - (a + b) • D := by
      simp only [smul_sub, add_smul]; abel
    rw [this, hab, one_smul]
  have hR : s • (a • (z₁ - D) + b • (z₂ - D)) = ((1 - l) * s₁) • (z₁ - D) + (l * s₂) • (z₂ - D) := by
    rw [smul_add, smul_smul, smul_smul, e1, e2]
  rw [key, hR]
  module

/-! ### Increments of a concave increasing function -/

/-- For concave `φ`, increments over intervals of equal length `L` decrease to the right. -/
theorem increment_anti {φ : ℝ → ℝ} (hc : ConcaveOn ℝ (Ioi 0) φ) {u₁ u₂ L : ℝ} (hu₁ : 0 < u₁) (hu : u₁ ≤ u₂)
    (hL : 0 < L) : φ (u₂ + L) - φ u₂ ≤ φ (u₁ + L) - φ u₁ := by
  set d := u₂ + L - u₁ with hd
  have hd0 : 0 < d := by linarith
  set t := L / d with ht
  have ht0 : 0 ≤ t := by positivity
  have ht1 : t ≤ 1 := by rw [ht, div_le_one hd0]; linarith
  have m1 : u₁ ∈ Ioi (0 : ℝ) := hu₁
  have m2 : u₂ + L ∈ Ioi (0 : ℝ) := by simp only [mem_Ioi]; linarith
  have c1 := hc.2 m1 m2 ht0 (by linarith : 0 ≤ 1 - t) (by ring)
  have c2 := hc.2 m1 m2 (by linarith : 0 ≤ 1 - t) ht0 (by ring)
  simp only [smul_eq_mul] at c1 c2
  have e1 : t * u₁ + (1 - t) * (u₂ + L) = u₂ := by rw [ht]; field_simp; ring
  have e2 : (1 - t) * u₁ + t * (u₂ + L) = u₁ + L := by rw [ht]; field_simp; ring
  rw [e1] at c1
  rw [e2] at c2
  linarith

/-- If `φ` is concave and strictly increasing on `(0, ∞)`, an interval `[u₁, v₁]` that is longer than `[u₂, v₂]` and
starts no later gains strictly more. -/
theorem increment_gt {φ : ℝ → ℝ} (hc : ConcaveOn ℝ (Ioi 0) φ) (hm : StrictMonoOn φ (Ioi 0))
    {u₁ v₁ u₂ v₂ : ℝ} (hu₁ : 0 < u₁) (hv₂ : u₂ < v₂) (hu : u₁ ≤ u₂) (hlen : v₂ - u₂ < v₁ - u₁) :
    φ v₂ - φ u₂ < φ v₁ - φ u₁ := by
  set L := v₂ - u₂ with hL
  have hL0 : 0 < L := by linarith
  have step1 : φ (u₁ + L) < φ v₁ := hm (by simp only [mem_Ioi]; linarith) (by simp only [mem_Ioi]; linarith)
    (by linarith)
  have step2 := increment_anti hc hu₁ hu hL0
  have : v₂ = u₂ + L := by rw [hL]; ring
  rw [this]
  linarith

/-- The log-likelihood ratio `y ↦ φ(1 - y/h₂) - φ(1 - y/h₁)` of the two height laws is strictly increasing on
`(0, h₁)` when `h₁ < h₂`. -/
theorem ratio_strictMono {φ : ℝ → ℝ} (hc : ConcaveOn ℝ (Ioi 0) φ) (hm : StrictMonoOn φ (Ioi 0))
    {h₁ h₂ y y' : ℝ} (hh₁ : 0 < h₁) (hh : h₁ < h₂) (hy : 0 ≤ y) (hyy : y < y') (hy' : y' < h₁) :
    φ (1 - y / h₂) - φ (1 - y / h₁) < φ (1 - y' / h₂) - φ (1 - y' / h₁) := by
  have hh₂ : 0 < h₂ := by linarith
  have k := increment_gt (u₁ := 1 - y' / h₁) (v₁ := 1 - y / h₁) (u₂ := 1 - y' / h₂) (v₂ := 1 - y / h₂) hc hm
    (by rw [sub_pos, div_lt_one hh₁]; exact hy')
    (by have : y / h₂ < y' / h₂ := div_lt_div_of_pos_right hyy hh₂; linarith)
    (by have : y' / h₂ ≤ y' / h₁ := div_le_div_of_nonneg_left (by linarith) hh₁ hh.le; linarith)
    (by
      have e1 : 1 - y / h₂ - (1 - y' / h₂) = (y' - y) / h₂ := by ring
      have e2 : 1 - y / h₁ - (1 - y' / h₁) = (y' - y) / h₁ := by ring
      rw [e1, e2]; exact div_lt_div_of_pos_left (by linarith) hh₁ hh)
  linarith

/-! ### Chebyshev's integral inequality -/

variable {μ : Measure ℝ} [IsFiniteMeasure μ] {f g : ℝ → ℝ}

/-- The double integral of `(f x - f y)(g x - g y)` is `2(μ(ℝ) ∫ fg - ∫ f ∫ g)`. -/
theorem double_integral (hf : Integrable f μ) (hg : Integrable g μ) (hfg : Integrable (fun x => f x * g x) μ) :
    ∫ z, (f z.1 - f z.2) * (g z.1 - g z.2) ∂(μ.prod μ)
      = 2 * ((μ univ).toReal * ∫ x, f x * g x ∂μ - (∫ x, f x ∂μ) * ∫ x, g x ∂μ) := by
  have i1 : Integrable (fun z : ℝ × ℝ => (f z.1 * g z.1) * (1 : ℝ)) (μ.prod μ) :=
    hfg.mul_prod (integrable_const 1)
  have i2 : Integrable (fun z : ℝ × ℝ => (1 : ℝ) * (f z.2 * g z.2)) (μ.prod μ) :=
    (integrable_const 1).mul_prod hfg
  have i3 : Integrable (fun z : ℝ × ℝ => f z.1 * g z.2) (μ.prod μ) := hf.mul_prod hg
  have i4 : Integrable (fun z : ℝ × ℝ => g z.1 * f z.2) (μ.prod μ) := hg.mul_prod hf
  have expand : ∀ z : ℝ × ℝ, (f z.1 - f z.2) * (g z.1 - g z.2)
      = (f z.1 * g z.1) * 1 + 1 * (f z.2 * g z.2) - f z.1 * g z.2 - g z.1 * f z.2 := by intro z; ring
  have i12 : Integrable (fun z : ℝ × ℝ => (f z.1 * g z.1) * 1 + 1 * (f z.2 * g z.2)) (μ.prod μ) := i1.add i2
  have i123 : Integrable (fun z : ℝ × ℝ => (f z.1 * g z.1) * 1 + 1 * (f z.2 * g z.2) - f z.1 * g z.2) (μ.prod μ) :=
    i12.sub i3
  simp only [expand]
  have p1 := integral_prod_mul (μ := μ) (ν := μ) (fun x => f x * g x) (fun _ => (1 : ℝ))
  have p2 := integral_prod_mul (μ := μ) (ν := μ) (fun _ => (1 : ℝ)) (fun x => f x * g x)
  have p3 := integral_prod_mul (μ := μ) (ν := μ) f g
  have p4 := integral_prod_mul (μ := μ) (ν := μ) g f
  rw [integral_sub i123 i4, integral_sub i12 i3, integral_add i1 i2, p1, p2, p3, p4]
  simp only [integral_const, smul_eq_mul, mul_one, measureReal_def]
  ring

/-- Chebyshev: for similarly ordered `f, g`, `∫ f ∫ g ≤ μ(ℝ) ∫ fg`. -/
theorem chebyshev (hf : Integrable f μ) (hg : Integrable g μ) (hfg : Integrable (fun x => f x * g x) μ)
    (hord : ∀ x y, 0 ≤ (f x - f y) * (g x - g y)) :
    (∫ x, f x ∂μ) * (∫ x, g x ∂μ) ≤ (μ univ).toReal * ∫ x, f x * g x ∂μ := by
  have h := double_integral hf hg hfg
  have : 0 ≤ ∫ z, (f z.1 - f z.2) * (g z.1 - g z.2) ∂(μ.prod μ) := integral_nonneg fun z => hord z.1 z.2
  linarith

/-- Strict Chebyshev: strict when `(f x - f y)(g x - g y) > 0` on a set of positive product measure. -/
theorem chebyshev_strict (hf : Integrable f μ) (hg : Integrable g μ) (hfg : Integrable (fun x => f x * g x) μ)
    (hord : ∀ x y, 0 ≤ (f x - f y) * (g x - g y))
    (hpos : 0 < (μ.prod μ) (Function.support (fun (z : ℝ × ℝ) => (f z.1 - f z.2) * (g z.1 - g z.2)))) :
    (∫ x, f x ∂μ) * (∫ x, g x ∂μ) < (μ univ).toReal * ∫ x, f x * g x ∂μ := by
  have h := double_integral hf hg hfg
  have hint : Integrable (fun z : ℝ × ℝ => (f z.1 - f z.2) * (g z.1 - g z.2)) (μ.prod μ) := by
    have i1 : Integrable (fun z : ℝ × ℝ => (f z.1 * g z.1) * (1 : ℝ)) (μ.prod μ) :=
      hfg.mul_prod (integrable_const 1)
    have i2 : Integrable (fun z : ℝ × ℝ => (1 : ℝ) * (f z.2 * g z.2)) (μ.prod μ) :=
      (integrable_const 1).mul_prod hfg
    have i3 : Integrable (fun z : ℝ × ℝ => f z.1 * g z.2) (μ.prod μ) := hf.mul_prod hg
    have i4 : Integrable (fun z : ℝ × ℝ => g z.1 * f z.2) (μ.prod μ) := hg.mul_prod hf
    have i1234 : Integrable (fun z : ℝ × ℝ =>
        (f z.1 * g z.1) * 1 + 1 * (f z.2 * g z.2) - f z.1 * g z.2 - g z.1 * f z.2) (μ.prod μ) :=
      ((i1.add i2).sub i3).sub i4
    refine i1234.congr (Filter.Eventually.of_forall fun (z : ℝ × ℝ) => ?_)
    simp only; ring
  have : 0 < ∫ z, (f z.1 - f z.2) * (g z.1 - g z.2) ∂(μ.prod μ) :=
    (integral_pos_iff_support_of_nonneg (fun (z : ℝ × ℝ) => hord z.1 z.2) hint).mpr hpos
  linarith

/-- Adding mass above the old range raises the mean: if the new mean is `p m₁ + (1 - p) m₂` with `p ≤ 1`,
`m₁ > m₀` and `m₂ ≥ m₁`, it exceeds `m₀`. -/
theorem mean_mix {p m₀ m₁ m₂ : ℝ} (hp1 : p ≤ 1) (h₁ : m₀ < m₁) (h₂ : m₁ ≤ m₂) :
    m₀ < p * m₁ + (1 - p) * m₂ := by
  nlinarith

end GaussianApex
