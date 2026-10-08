import EnclosingCopy.Enclosing.PolygonSampling
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Homothetic contraction of the physical polygon

Support gaps characterize the contracted polygon exactly. Planar Lebesgue measure
scales quadratically, and every supporting depth level has measure zero.
-/
namespace Enclosing
open MeasureTheory Set
open scoped Pointwise
variable {m : ℕ} (K : Sides m)

def contractAt (w : ℝ × ℝ) (t : ℝ) (x : ℝ × ℝ) : ℝ × ℝ :=
  w + (1 - t) • (x - w)

def contractedRegion (w : ℝ × ℝ) (t : ℝ) : Set (ℝ × ℝ) :=
  contractAt w t '' polygonRegion K

lemma continuous_contractAt (w : ℝ × ℝ) (t : ℝ) : Continuous (contractAt w t) := by
  unfold contractAt; fun_prop

lemma gap_contractAt (w x : ℝ × ℝ) (t : ℝ) (i : Fin m) :
    K.h i - dot (contractAt w t x) (K.u i) =
      (1 - t) * (K.h i - dot x (K.u i)) + t * (K.h i - dot w (K.u i)) := by
  dsimp [contractAt, dot]
  ring

lemma mem_contractedRegion_iff (w : ℝ × ℝ) {t : ℝ} (ht : t < 1) (x : ℝ × ℝ) :
    x ∈ contractedRegion K w t ↔
      ∀ i, t * (K.h i - dot w (K.u i)) ≤ K.h i - dot x (K.u i) := by
  have hr : 0 < 1 - t := sub_pos.mpr ht
  constructor
  · rintro ⟨z, hz, rfl⟩ i
    rw [gap_contractAt]
    have hgap : 0 ≤ K.h i - dot z (K.u i) := sub_nonneg.mpr (hz i)
    nlinarith [mul_nonneg hr.le hgap]
  · intro hx
    let z := w + (1 - t)⁻¹ • (x - w)
    have he : contractAt w t z = x := by
      simp only [contractAt, z, add_sub_cancel_left, smul_smul,
        mul_inv_cancel₀ hr.ne', one_smul, add_sub_cancel]
    refine ⟨z, ?_, he⟩
    intro i
    have hg := gap_contractAt K w z t i
    rw [he] at hg
    have hi := hx i
    nlinarith

lemma contractedRegion_subset {w : ℝ × ℝ} (hw : w ∈ polygonRegion K)
    {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) : contractedRegion K w t ⊆ polygonRegion K := by
  rintro x ⟨z, hz, rfl⟩ i
  have hg := gap_contractAt K w z t i
  have hzi : 0 ≤ K.h i - dot z (K.u i) := sub_nonneg.mpr (hz i)
  have hwi : 0 ≤ K.h i - dot w (K.u i) := sub_nonneg.mpr (hw i)
  nlinarith [mul_nonneg (sub_nonneg.mpr h1) hzi, mul_nonneg h0 hwi]

variable [NeZero m]

lemma isCompact_contractedRegion (hG : GoodSides K) (w : ℝ × ℝ) (t : ℝ) :
    IsCompact (contractedRegion K w t) :=
  (isCompact_polygonRegion K hG).image (continuous_contractAt w t)

omit [NeZero m] in
lemma contractedRegion_volume (w : ℝ × ℝ) (t : ℝ) :
    volume (contractedRegion K w t) =
      ENNReal.ofReal ((1 - t) ^ 2) * volume (polygonRegion K) := by
  have he : contractedRegion K w t = (fun x => w + x) ''
      ((1 - t) • ((fun x => -w + x) '' polygonRegion K)) := by
    unfold contractedRegion
    rw [← image_smul, image_image, image_image]
    congr 1
    funext x
    simp only [contractAt, sub_eq_add_neg, add_comm]
  rw [he, image_add_left, measure_preimage_add, Measure.addHaar_smul,
    Module.finrank_prod, Module.finrank_self]
  change ENNReal.ofReal |(1 - t) ^ 2| * volume ((fun x => -w + x) '' polygonRegion K) = _
  rw [abs_of_nonneg (sq_nonneg _), image_add_left, measure_preimage_add]

omit [NeZero m] in
lemma contractedRegion_real_volume (w : ℝ × ℝ) (t : ℝ) :
    volume.real (contractedRegion K w t) = (1 - t) ^ 2 * volume.real (polygonRegion K) := by
  rw [measureReal_def, contractedRegion_volume, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (sq_nonneg _), measureReal_def]

omit [NeZero m] in
/-- Any fixed depth level of a unit support normal is a Lebesgue-null line. -/
lemma depth_level_volume_zero (hG : GoodSides K) (i : Fin m) (d : ℝ) :
    volume {x | K.h i - dot x (K.u i) = d} = 0 := by
  let e := sideEquiv (K.u i) (hG.unit i) (K.h i)
  have hp : MeasurePreserving e volume volume := sideChart_preserving _ (hG.unit i) _
  have he : {x | K.h i - dot x (K.u i) = d} =
      e.symm ⁻¹' (univ ×ˢ {d}) := by ext x; simp [e, sideEquiv, sideCoords]
  rw [he, hp.symm.measure_preimage
    (MeasurableSet.univ.prod (measurableSet_singleton d)).nullMeasurableSet,
    Measure.volume_eq_prod, Measure.prod_prod, Real.volume_singleton, mul_zero]

end Enclosing
