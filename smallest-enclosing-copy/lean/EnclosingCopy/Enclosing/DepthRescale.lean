import EnclosingCopy.Enclosing.PolygonOverlap

/-!
# Exact laws under inward-depth rescaling

The physical side chart followed by `D = r d` has Jacobian `r`. Restricting planar
Lebesgue measure to a physical window of depth `T/r` and mapping to `(s,D)` gives
exactly `r⁻¹` times Lebesgue measure on the fixed rectangle. This is the spatial
mark-law bridge for actual polygon samples.
-/
namespace Enclosing
open MeasureTheory Set Filter Topology

/-- Multiply inward depth while preserving side position. -/
def depthScale (r : ℝ) (q : ℝ × ℝ) : ℝ × ℝ := (q.1, r * q.2)

lemma continuous_depthScale (r : ℝ) : Continuous (depthScale r) := by
  unfold depthScale; fun_prop

/-- Depth scaling as a measurable equivalence for nonzero scale. -/
noncomputable def depthScaleEquiv (r : ℝ) (hr : r ≠ 0) : (ℝ × ℝ) ≃ᵐ (ℝ × ℝ) where
  toFun := depthScale r
  invFun := depthScale r⁻¹
  left_inv q := by ext <;> simp [depthScale, hr]
  right_inv q := by ext <;> simp [depthScale, hr]
  measurable_toFun := (continuous_depthScale r).measurable
  measurable_invFun := (continuous_depthScale r⁻¹).measurable

/-- The physical Jacobian for rescaling the inward depth alone. -/
theorem depthScale_map_volume (r : ℝ) (hr : 0 < r) :
    Measure.map (depthScale r) volume = ENNReal.ofReal r⁻¹ • volume := by
  have he : depthScale r = doubleDepth (-1, 0) (0, -r) 0 0 := by
    funext q; ext <;> simp [depthScale, doubleDepth, dot, mul_comm]
  rw [he, doubleDepth_map_volume _ _ _ _ (by simp [cross, hr.ne'])]
  simp only [cross, neg_mul, one_mul, mul_neg, neg_neg, zero_mul, sub_zero,
    abs_of_pos hr]

/-- Physical coordinates to position and rescaled inward depth. -/
noncomputable def scaledSideEquiv (u : ℝ × ℝ) (hu : u.1 ^ 2 + u.2 ^ 2 = 1) (h r : ℝ)
    (hr : r ≠ 0) : (ℝ × ℝ) ≃ᵐ (ℝ × ℝ) :=
  (sideEquiv u hu h).symm.trans (depthScaleEquiv r hr)

lemma scaledSideEquiv_apply (u : ℝ × ℝ) (hu : u.1 ^ 2 + u.2 ^ 2 = 1)
    (h r : ℝ) (hr : r ≠ 0) (x : ℝ × ℝ) :
    scaledSideEquiv u hu h r hr x = (dot x (sideTangent u), r * (h - dot x u)) := rfl

/-- The rescaled coordinate map has the expected planar measure factor. -/
theorem scaledSideEquiv_map_volume (u : ℝ × ℝ) (hu : u.1 ^ 2 + u.2 ^ 2 = 1)
    (h r : ℝ) (hr : 0 < r) :
    Measure.map (scaledSideEquiv u hu h r hr.ne') volume = ENNReal.ofReal r⁻¹ • volume := by
  have hs : MeasurePreserving (sideEquiv u hu h) volume volume := sideChart_preserving u hu h
  rw [show (scaledSideEquiv u hu h r hr.ne' : (ℝ × ℝ) → ℝ × ℝ) =
      depthScale r ∘ (sideEquiv u hu h).symm from rfl,
    ← Measure.map_map (continuous_depthScale r).measurable hs.symm.measurable,
    hs.symm.map_eq, depthScale_map_volume r hr]

lemma depthScale_preimage_rectangle (r : ℝ) (hr : 0 < r) (a b T : ℝ) :
    depthScale r ⁻¹' (Icc a b ×ˢ Icc 0 T) = Icc a b ×ˢ Icc 0 (T / r) := by
  ext q
  simp only [mem_preimage, mem_prod, mem_Icc, depthScale]
  have hnonneg : 0 ≤ r * q.2 ↔ 0 ≤ q.2 := mul_nonneg_iff_of_pos_left hr
  rw [hnonneg]
  simp only [le_div_iff₀ hr, mul_comm]

/-- A thin physical side rectangle is exactly the preimage of the fixed mark rectangle. -/
theorem scaledSideEquiv_preimage_rectangle (u : ℝ × ℝ)
    (hu : u.1 ^ 2 + u.2 ^ 2 = 1) (h r : ℝ) (hr : 0 < r) (a b T : ℝ) :
    scaledSideEquiv u hu h r hr.ne' ⁻¹' (Icc a b ×ˢ Icc 0 T) =
      sideChart u h '' (Icc a b ×ˢ Icc 0 (T / r)) := by
  change (depthScale r ∘ (sideEquiv u hu h).symm) ⁻¹' _ = _
  rw [preimage_comp, depthScale_preimage_rectangle r hr]
  exact ((sideEquiv u hu h).image_eq_preimage_symm _).symm

/-- Exact law of rescaled coordinates under restricted planar Lebesgue measure. -/
theorem scaledSideEquiv_restrict_volume (u : ℝ × ℝ)
    (hu : u.1 ^ 2 + u.2 ^ 2 = 1) (h r : ℝ) (hr : 0 < r) (a b T : ℝ) :
    Measure.map (scaledSideEquiv u hu h r hr.ne')
      (volume.restrict (sideChart u h '' (Icc a b ×ˢ Icc 0 (T / r)))) =
      ENNReal.ofReal r⁻¹ • volume.restrict (Icc a b ×ˢ Icc 0 T) := by
  rw [← scaledSideEquiv_preimage_rectangle u hu h r hr a b T,
    ← (scaledSideEquiv u hu h r hr.ne').restrict_map,
    scaledSideEquiv_map_volume u hu h r hr, Measure.restrict_smul]

end Enclosing
