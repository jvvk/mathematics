import EnclosingCopy.Enclosing.DepthRescale
import EnclosingCopy.Poisson.ConditionalWindow

/-!
# Conditional marks on a trimmed physical side window

Rescaled marks of a uniform polygon point conditioned to a contained side rectangle
have exactly the fixed uniform rectangle law. For trimmed intervals this identity
holds for every sufficiently large sample size, not merely in the limit.
-/
namespace Enclosing
open MeasureTheory Set Filter Topology

/-- The fixed uniform law of side position and scaled depth. -/
noncomputable def rectangleLaw (a b T : ℝ) : Measure (ℝ × ℝ) :=
  ProbabilityTheory.cond volume (Icc a b ×ˢ Icc 0 T)

lemma rectangle_volume (a b T : ℝ) : volume (Icc a b ×ˢ Icc (0 : ℝ) T) =
    ENNReal.ofReal (b - a) * ENNReal.ofReal T := by
  rw [Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Icc, Real.volume_Icc, sub_zero]

lemma rectangleLaw_probability (a b T : ℝ) (hab : a < b) (hT : 0 < T) :
    IsProbabilityMeasure (rectangleLaw a b T) := by
  apply ProbabilityTheory.cond_isProbabilityMeasure_of_finite
  · rw [rectangle_volume]
    exact mul_ne_zero (ENNReal.ofReal_pos.mpr (sub_pos.mpr hab)).ne' (ENNReal.ofReal_pos.mpr hT).ne'
  · rw [rectangle_volume]; finiteness

/-- The measurable rescaled side mark, also defined at sample size zero. -/
def sideMark {m : ℕ} (K : Sides m) (i : Fin m) (n : ℕ) (x : ℝ × ℝ) : ℝ × ℝ :=
  depthScale n (sideCoords (K.u i) (K.h i) x)

lemma measurable_sideMark {m : ℕ} (K : Sides m) (i : Fin m) (n : ℕ) :
    Measurable (sideMark K i n) :=
  (continuous_depthScale n).measurable.comp (continuous_sideCoords _ _).measurable

variable {m : ℕ} [NeZero m] {v : Fin m → ℝ × ℝ}

/-- The physical uniform law restricts to a contained window with constant area density. -/
theorem polygonSample_restrict_sideWindow (hm : 3 ≤ m) (hv : ConvexPos v) (harea : area v = 1)
    (i : Fin m) (a b d : ℝ)
    (hsub : sideWindow (sidesOf v hm hv harea) i a b d ⊆
      polygonRegion (sidesOf v hm hv harea)) :
    (polygonSample v hm hv harea).restrict (sideWindow (sidesOf v hm hv harea) i a b d) =
      (volume (polygonRegion (sidesOf v hm hv harea)))⁻¹ •
        volume.restrict (sideWindow (sidesOf v hm hv harea) i a b d) := by
  rw [polygonSample, ProbabilityTheory.cond, Measure.restrict_smul,
    Measure.restrict_restrict (measurableSet_sideWindow _ _ _ _ _),
    inter_eq_left.mpr hsub]

/-- Exact unnormalized rescaled spatial law on a contained side rectangle. -/
theorem mapped_polygon_sideWindow (hm : 3 ≤ m) (hv : ConvexPos v) (harea : area v = 1)
    (i : Fin m) (a b T : ℝ) (n : ℕ) (hn : 0 < n)
    (hsub : sideWindow (sidesOf v hm hv harea) i a b (T / n) ⊆
      polygonRegion (sidesOf v hm hv harea)) :
    let K := sidesOf v hm hv harea
    Measure.map (sideMark K i n)
      ((polygonSample v hm hv harea).restrict (sideWindow K i a b (T / n))) =
      ((volume (polygonRegion K))⁻¹ * ENNReal.ofReal (n : ℝ)⁻¹) •
        volume.restrict (Icc a b ×ˢ Icc 0 T) := by
  intro K
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have he : sideMark K i n = scaledSideEquiv (K.u i)
      ((goodSides_of_convex hm hv harea).unit i) (K.h i) n hn'.ne' := rfl
  rw [polygonSample_restrict_sideWindow hm hv harea i a b _ hsub,
    Measure.map_smul _ (measurable_sideMark K i n).aemeasurable,
    he]
  dsimp only [sideWindow, K]
  rw [scaledSideEquiv_restrict_volume _ _ _ _ hn', smul_smul]

/-- **The conditional rescaled mark law is exactly the fixed uniform rectangle law.** -/
theorem mapped_polygon_sideWindowLaw (hm : 3 ≤ m) (hv : ConvexPos v) (harea : area v = 1)
    (i : Fin m) {a b T : ℝ} (hab : a < b) (hT : 0 < T) (n : ℕ) (hn : 0 < n)
    (hsub : sideWindow (sidesOf v hm hv harea) i a b (T / n) ⊆
      polygonRegion (sidesOf v hm hv harea)) :
    let K := sidesOf v hm hv harea
    Measure.map (sideMark K i n) (PoissonPP.windowLaw (polygonSample v hm hv harea)
      (sideWindow K i a b (T / n))) = rectangleLaw a b T := by
  intro K
  let R := Icc a b ×ˢ Icc (0 : ℝ) T
  let Λ := (volume : Measure (ℝ × ℝ)).restrict R
  have hΛ : Λ univ ≠ 0 := by
    rw [Measure.restrict_apply_univ, rectangle_volume]
    exact mul_ne_zero (ENNReal.ofReal_pos.mpr (sub_pos.mpr hab)).ne' (ENNReal.ofReal_pos.mpr hT).ne'
  have : IsFiniteMeasure Λ := isFiniteMeasure_restrict.2 (by
    rw [rectangle_volume]; finiteness)
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hc : (volume (polygonRegion K))⁻¹ * ENNReal.ofReal (n : ℝ)⁻¹ ≠ 0 :=
    mul_ne_zero (ENNReal.inv_ne_zero.mpr
      (polygonRegion_volume_ne_top K (goodSides_of_convex hm hv harea)))
      (ENNReal.ofReal_pos.mpr (inv_pos.mpr hn')).ne'
  have hct : (volume (polygonRegion K))⁻¹ * ENNReal.ofReal (n : ℝ)⁻¹ ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr (polygonRegion_volume_pos hm hv harea).ne')
      ENNReal.ofReal_ne_top
  have he := PoissonPP.mapped_windowLaw (polygonSample v hm hv harea)
    (sideWindow K i a b (T / n)) (sideMark K i n) (measurable_sideMark K i n)
    Λ hΛ _ hc hct (mapped_polygon_sideWindow hm hv harea i a b T n hn hsub)
  simpa only [Λ, R, Measure.restrict_apply_univ, rectangleLaw, ProbabilityTheory.cond] using he

/-- The conditional rectangle law is independent of sample size once the window is shallow. -/
theorem sideMarkLaw_eventually (hm : 3 ≤ m) (hv : ConvexPos v) (harea : area v = 1)
    (i : Fin m) {a b T : ℝ} (ha : aEnd v i < a) (hab : a < b)
    (hb : b < bEnd v i) (hT : 0 < T) :
    let K := sidesOf v hm hv harea
    ∀ᶠ n : ℕ in atTop, Measure.map (sideMark K i n)
      (PoissonPP.windowLaw (polygonSample v hm hv harea) (sideWindow K i a b (T / n))) =
        rectangleLaw a b T := by
  intro K
  obtain ⟨d₀, hd₀, hsub⟩ := exists_sideWindow_subset hm hv harea i ha hab.le hb
  have hsmall := (tendsto_const_div_atTop_nhds_zero_nat T).eventually (Iio_mem_nhds hd₀)
  filter_upwards [hsmall, eventually_gt_atTop 0] with n hn hnpos
  apply mapped_polygon_sideWindowLaw hm hv harea i hab hT n hnpos
  exact hsub _ ⟨div_nonneg hT.le (Nat.cast_nonneg n), hn.le⟩

end Enclosing
