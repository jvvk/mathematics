import EnclosingCopy.Enclosing.VertexCount
import EnclosingCopy.Enclosing.Segment

/-!
# The three-point depth-to-copy coordinates in the segment case

The two points on one side and the point on its opposite side determine scale,
normal translation, and tilt. Their depth map has Jacobian
`(s₂ - s₁) * (h₁ + h₂)`. This supplies the change-of-variables step of the
three-point Mecke calculation, independently of the probability calculation.
-/

namespace Enclosing
open MeasureTheory Matrix ENNReal

def segmentMatrix (h₁ h₂ s₁ s₂ s₃ : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![h₁, 1, -s₁; h₁, 1, -s₂; h₂, -1, -s₃]

lemma segmentMatrix_det (h₁ h₂ s₁ s₂ s₃ : ℝ) :
    (segmentMatrix h₁ h₂ s₁ s₂ s₃).det = -(s₂ - s₁) * (h₁ + h₂) := by
  rw [Matrix.det_fin_three]
  simp [segmentMatrix]
  ring

lemma segmentMatrix_abs_det (h₁ h₂ s₁ s₂ s₃ : ℝ) (h12 : s₁ < s₂) (hw : 0 < h₁ + h₂) :
    |(segmentMatrix h₁ h₂ s₁ s₂ s₃).det| = (s₂ - s₁) * (h₁ + h₂) := by
  rw [segmentMatrix_det, abs_mul, abs_neg, abs_of_pos (sub_pos.mpr h12), abs_of_pos hw]

lemma segmentMatrix_nonsingular (h₁ h₂ s₁ s₂ s₃ : ℝ) (h12 : s₁ < s₂) (hw : 0 < h₁ + h₂) :
    (segmentMatrix h₁ h₂ s₁ s₂ s₃).det ≠ 0 := by
  rw [segmentMatrix_det]
  exact mul_ne_zero (neg_ne_zero.mpr (sub_pos.mpr h12).ne') hw.ne'

/-- The depth-to-coordinate Jacobian for an arbitrary square real matrix.
In particular, this applies to the three transverse segment coordinates. -/
theorem lintegral_inverse_depths {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ) (hA : A.det ≠ 0)
    (f : (Fin d → ℝ) → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ D : Fin d → ℝ, f (A⁻¹ *ᵥ (-D))) =
      ENNReal.ofReal |A.det| * ∫⁻ z : Fin d → ℝ, f z := by
  have habs : |(-A⁻¹).det| = |A.det|⁻¹ := by
    simp [Matrix.det_neg, Matrix.det_nonsing_inv, Ring.inverse_eq_inv, abs_mul, abs_inv]
  have hb : (-A⁻¹).det ≠ 0 := by
    apply abs_ne_zero.mp
    rw [habs]
    exact inv_ne_zero (abs_ne_zero.mpr hA)
  have hm := Real.map_matrix_volume_pi_eq_smul_volume_pi hb
  have hc : Measurable (Matrix.toLin' (-A⁻¹)) :=
    (LinearMap.continuous_on_pi _).measurable
  have hs : ENNReal.ofReal |((-A⁻¹).det)⁻¹| = ENNReal.ofReal |A.det| := by
    rw [abs_inv, habs, inv_inv]
  calc (∫⁻ D : Fin d → ℝ, f (A⁻¹ *ᵥ (-D)))
      = ∫⁻ D : Fin d → ℝ, f (Matrix.toLin' (-A⁻¹) D) := by
        congr 1; funext D
        rw [Matrix.toLin'_apply, Matrix.neg_mulVec, Matrix.mulVec_neg]
    _ = ∫⁻ z : Fin d → ℝ, f z ∂(Measure.map (Matrix.toLin' (-A⁻¹)) volume) :=
      (lintegral_map hf hc).symm
    _ = _ := by rw [hm, lintegral_smul_measure, hs]; rfl

/-- Both segment Jacobian factors together, in the actual three-point depth map. -/
theorem segment_lintegral_depths (h₁ h₂ s₁ s₂ s₃ : ℝ)
    (h12 : s₁ < s₂) (hw : 0 < h₁ + h₂)
    (f : (Fin 3 → ℝ) → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ D : Fin 3 → ℝ, f ((segmentMatrix h₁ h₂ s₁ s₂ s₃)⁻¹ *ᵥ (-D))) =
      ENNReal.ofReal ((s₂ - s₁) * (h₁ + h₂)) * ∫⁻ z : Fin 3 → ℝ, f z := by
  rw [lintegral_inverse_depths _ (segmentMatrix_nonsingular _ _ _ _ _ h12 hw) f hf,
    segmentMatrix_abs_det _ _ _ _ _ h12 hw]

end Enclosing
