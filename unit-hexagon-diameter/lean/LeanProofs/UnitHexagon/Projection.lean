import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Convex.Join
import Mathlib.Tactic

/-!
# Unit hexagons: the four-point projection lemma (Lemma 2.2)

For a unit chain `X₀, X₁, X₂, X₃` with `|X₀X₂| ≤ √2` and `X₃ ≠ X₁`, project onto `b = X₁ - X₂` from `X₂`.
The projection is `1` at `X₁`, `0` at `X₂`, `|X₀ - X₂|²/2 ≤ 1` at `X₀`, and `< 1` at `X₃`. A convex
combination of `X₀, X₂, X₃` can reach `1` only at `X₀` itself, so `X₁ ∉ conv(X₀, X₂, X₃)`.
The statement holds in any real inner product space.
-/

namespace UnitHexagon

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

open RealInnerProductSpace

/-- Weighted form of Lemma 2.2. -/
theorem projection_weights {X₀ X₁ X₂ X₃ : V} (h01 : ‖X₀ - X₁‖ = 1) (h12 : ‖X₁ - X₂‖ = 1)
    (h23 : ‖X₃ - X₂‖ = 1) (h02 : ‖X₀ - X₂‖ ≤ Real.sqrt 2) (h31 : X₃ ≠ X₁) (h10 : X₀ ≠ X₁)
    {w₀ w₂ w₃ : ℝ} (hw₀ : 0 ≤ w₀) (hw₂ : 0 ≤ w₂) (hw₃ : 0 ≤ w₃) (hw : w₀ + w₂ + w₃ = 1) :
    X₁ ≠ w₀ • X₀ + w₂ • X₂ + w₃ • X₃ := by
  intro hX
  set b := X₁ - X₂
  set f₀ := ⟪X₀ - X₂, b⟫
  set f₃ := ⟪X₃ - X₂, b⟫
  have hb : ⟪b, b⟫ = 1 := by rw [real_inner_self_eq_norm_sq, h12]; norm_num
  -- projection of X₀ is |X₀ - X₂|² / 2 ≤ 1
  have e0 : X₀ - X₁ = (X₀ - X₂) - b := by simp [b]
  have hf0 : 2 * f₀ = ‖X₀ - X₂‖ ^ 2 := by
    have := congrArg (fun v => ‖v‖ ^ 2) e0
    simp only [h01] at this
    rw [@norm_sub_sq_real, ← real_inner_self_eq_norm_sq b, hb] at this
    linarith
  have hsq : ‖X₀ - X₂‖ ^ 2 ≤ 2 := by
    have := pow_le_pow_left₀ (norm_nonneg _) h02 2
    rwa [Real.sq_sqrt (by norm_num)] at this
  have hf0le : f₀ ≤ 1 := by linarith
  -- projection of X₃ is strictly less than one
  have e3 : X₃ - X₁ = (X₃ - X₂) - b := by simp [b]
  have hf3 : f₃ < 1 := by
    have hpos : 0 < ‖X₃ - X₁‖ := norm_pos_iff.2 (sub_ne_zero.2 h31)
    have h := norm_sub_sq_real (X₃ - X₂) b
    rw [← e3, h23, h12] at h
    nlinarith
  -- project the convex combination
  have ecomb : b = w₀ • (X₀ - X₂) + w₃ • (X₃ - X₂) := by
    have : w₂ = 1 - w₀ - w₃ := by linarith
    simp only [b, hX, this, smul_sub, sub_smul, one_smul]
    abel
  have key : 1 = w₀ * f₀ + w₃ * f₃ := by
    rw [← hb]
    calc ⟪b, b⟫ = ⟪w₀ • (X₀ - X₂) + w₃ • (X₃ - X₂), b⟫ := by nth_rewrite 1 [ecomb]; rfl
      _ = w₀ * f₀ + w₃ * f₃ := by rw [inner_add_left, real_inner_smul_left, real_inner_smul_left]
  have hw3 : w₃ = 0 := by
    by_contra h3
    have h3p : 0 < w₃ := lt_of_le_of_ne hw₃ (Ne.symm h3)
    nlinarith [mul_le_mul_of_nonneg_left hf0le hw₀, mul_lt_mul_of_pos_left hf3 h3p]
  have hw0 : w₀ = 1 := by
    rw [hw3] at key hw
    nlinarith [mul_le_mul_of_nonneg_left hf0le hw₀]
  have hw2 : w₂ = 0 := by linarith
  apply h10
  rw [hX, hw0, hw2, hw3]; simp

/-- Lemma 2.2: the middle point `X₁` is not in the convex hull of `X₀, X₂, X₃`. -/
theorem projection {X₀ X₁ X₂ X₃ : V} (h01 : ‖X₀ - X₁‖ = 1) (h12 : ‖X₁ - X₂‖ = 1)
    (h23 : ‖X₃ - X₂‖ = 1) (h02 : ‖X₀ - X₂‖ ≤ Real.sqrt 2) (h31 : X₃ ≠ X₁) (h10 : X₀ ≠ X₁) :
    X₁ ∉ convexHull ℝ ({X₀, X₂, X₃} : Set V) := by
  intro hmem
  rw [convexHull_insert (by simp), convexHull_pair, convexJoin_singleton_left] at hmem
  simp only [Set.mem_iUnion] at hmem
  obtain ⟨y, ⟨c₂, c₃, hc₂, hc₃, hc, rfl⟩, d₀, d₁, hd₀, hd₁, hd, hX⟩ := hmem
  apply projection_weights h01 h12 h23 h02 h31 h10 hd₀ (mul_nonneg hd₁ hc₂)
    (mul_nonneg hd₁ hc₃) (by linear_combination hd + d₁ * hc)
  rw [← hX, smul_add, smul_smul, smul_smul, add_assoc]

end UnitHexagon
