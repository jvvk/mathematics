import EnclosingCopy.Enclosing.PolygonRegion
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan

/-!
# Exact similarity coordinates for the finite enclosing problem

Tangent rather than angle coordinates make every sample containment constraint
exactly linear. The scale objective carries the nonlinear correction.
-/
namespace Enclosing
open Set Real

/-- Unnormalized rotation by tangent `t`. -/
def tangentRotate (t : ℝ) (x : ℝ × ℝ) : ℝ × ℝ :=
  (x.1 - t * x.2, x.2 + t * x.1)

/-- Ordinary planar rotation. -/
noncomputable def planeRotate (θ : ℝ) (x : ℝ × ℝ) : ℝ × ℝ :=
  (cos θ * x.1 - sin θ * x.2, sin θ * x.1 + cos θ * x.2)

lemma tangentRotate_neg (t : ℝ) (x : ℝ × ℝ) :
    tangentRotate (-t) (tangentRotate t x) = (1 + t ^ 2) • x := by
  apply Prod.ext <;> simp [tangentRotate] <;> ring

lemma tangentRotate_dot (t : ℝ) (x u : ℝ × ℝ) :
    dot (tangentRotate (-t) x) u = dot x u + t * dot x (sideTangent u) := by
  simp only [tangentRotate, sideTangent, dot]; ring

lemma planeRotate_arctan (t : ℝ) (x : ℝ × ℝ) :
    planeRotate (arctan t) x = (1 / sqrt (1 + t ^ 2)) • tangentRotate t x := by
  apply Prod.ext <;> simp [planeRotate, tangentRotate, cos_arctan, sin_arctan] <;> ring

/-- `q` is the inverse sample size, and `z` is the scaled LP coordinate. -/
noncomputable def tangentSimilarity (q : ℝ) (z : Copy) (x : ℝ × ℝ) : ℝ × ℝ :=
  (1 / (1 + (q * z.2.2) ^ 2)) •
    tangentRotate (q * z.2.2) ((1 + q * z.1) • x + q • z.2.1)

/-- Physical scale of the similarity in tangent coordinates. -/
noncomputable def tangentScale (q : ℝ) (z : Copy) : ℝ :=
  (1 + q * z.1) / sqrt (1 + (q * z.2.2) ^ 2)

/-- Physical translation of the similarity. -/
noncomputable def tangentShift (q : ℝ) (z : Copy) : ℝ × ℝ :=
  (1 / (1 + (q * z.2.2) ^ 2)) • tangentRotate (q * z.2.2) (q • z.2.1)

lemma tangentSimilarity_is_similarity (q : ℝ) (z : Copy) (x : ℝ × ℝ) :
    tangentSimilarity q z x =
      tangentScale q z • planeRotate (arctan (q * z.2.2)) x + tangentShift q z := by
  have hs : sqrt (1 + (q * z.2.2) ^ 2) ≠ 0 :=
    ne_of_gt (sqrt_pos.2 (by positivity))
  have he := sq_sqrt (show 0 ≤ 1 + (q * z.2.2) ^ 2 by positivity)
  simp only [mul_pow] at he
  rw [planeRotate_arctan]
  apply Prod.ext <;>
    simp [tangentSimilarity, tangentScale, tangentShift, tangentRotate] <;>
    field_simp <;> rw [he] <;> ring

lemma tangentScale_pos {q : ℝ} {z : Copy} (hz : 0 < 1 + q * z.1) :
    0 < tangentScale q z := div_pos hz (sqrt_pos.2 (by positivity))

lemma tangentSimilarity_inverse (q : ℝ) (z : Copy) (x : ℝ × ℝ) :
    tangentRotate (-(q * z.2.2)) (tangentSimilarity q z x) =
      (1 + q * z.1) • x + q • z.2.1 := by
  have hd : 1 + (q * z.2.2) ^ 2 ≠ 0 := ne_of_gt (by positivity)
  apply Prod.ext <;> simp [tangentSimilarity, tangentRotate] <;> field_simp <;> ring

lemma tangentSimilarity_inverse_right {q : ℝ} {z : Copy}
    (hz : 1 + q * z.1 ≠ 0) (x : ℝ × ℝ) :
    tangentSimilarity q z ((1 / (1 + q * z.1)) •
      (tangentRotate (-(q * z.2.2)) x - q • z.2.1)) = x := by
  have hd : 1 + (q * z.2.2) ^ 2 ≠ 0 := ne_of_gt (by positivity)
  apply Prod.ext <;> simp [tangentSimilarity, tangentRotate] <;> field_simp <;> ring

/-- The actual image of the physical polygon under a similarity. -/
noncomputable def tangentCopyRegion {m : ℕ} (K : Sides m) (q : ℝ) (z : Copy) :
    Set (ℝ × ℝ) := tangentSimilarity q z '' polygonRegion K

variable {m : ℕ} (K : Sides m)

/-- Exact physical containment, with no Taylor remainder. -/
theorem mem_tangentCopyRegion_iff {q : ℝ} {z : Copy}
    (hz : 0 < 1 + q * z.1) (x : ℝ × ℝ) :
    x ∈ tangentCopyRegion K q z ↔ ∀ i,
      dot x (K.u i) + q * z.2.2 * dot x (sideTangent (K.u i)) ≤
        (1 + q * z.1) * K.h i + q * dot z.2.1 (K.u i) := by
  constructor
  · rintro ⟨y, hy, rfl⟩ i
    rw [← tangentRotate_dot, tangentSimilarity_inverse]
    have hd : dot ((1 + q * z.1) • y + q • z.2.1) (K.u i) =
        (1 + q * z.1) * dot y (K.u i) + q * dot z.2.1 (K.u i) := by
      simp [dot]; ring
    rw [hd]
    exact add_le_add (mul_le_mul_of_nonneg_left (hy i) hz.le) le_rfl
  · intro hx
    refine ⟨(1 / (1 + q * z.1)) •
      (tangentRotate (-(q * z.2.2)) x - q • z.2.1), ?_,
      tangentSimilarity_inverse_right hz.ne' x⟩
    intro i
    have hd : dot ((1 / (1 + q * z.1)) •
        (tangentRotate (-(q * z.2.2)) x - q • z.2.1)) (K.u i) =
        (dot x (K.u i) + q * z.2.2 * dot x (sideTangent (K.u i)) -
          q * dot z.2.1 (K.u i)) / (1 + q * z.1) := by
      simp [dot, tangentRotate, sideTangent]; ring
    rw [hd, div_le_iff₀ hz]
    linarith [hx i]

/-- Side mark at physical depth scale `q`. -/
noncomputable def tangentPointMark (q : ℝ) (i : Fin m) (x : ℝ × ℝ) : Pt m :=
  (i, dot x (sideTangent (K.u i)), (K.h i - dot x (K.u i)) / q)

/-- Sample containment is exactly the model LP, simultaneously for all sides. -/
theorem mem_tangentCopyRegion_iff_model {q : ℝ} (hq : 0 < q) {z : Copy}
    (hz : 0 < 1 + q * z.1) (x : ℝ × ℝ) :
    x ∈ tangentCopyRegion K q z ↔
      ∀ i, ¬ violates K z (tangentPointMark K q i x) := by
  rw [mem_tangentCopyRegion_iff K hz]
  apply forall_congr'
  intro i
  simp only [violates, tangentPointMark, Hs, not_lt]
  rw [← sub_le_iff_le_add, le_div_iff₀ hq]
  constructor <;> intro h <;> nlinarith

end Enclosing
