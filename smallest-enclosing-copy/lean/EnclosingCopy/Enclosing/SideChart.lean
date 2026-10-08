import EnclosingCopy.Enclosing.ConvexPolygon
import EnclosingCopy.Poisson.IIDBounds
import Mathlib.Probability.ConditionalProbability

/-!
# Exact side-coordinate charts

For a unit outward normal `u` and support `h`, `(s,d)` represents the physical point
`(h-d)u + s R90(u)`. The chart and its inverse are explicit and preserve planar
Lebesgue measure. Thus a side rectangle has exactly its coordinate area.
-/
namespace Enclosing
open MeasureTheory Set Matrix

/-- The positively oriented tangent to a normal. -/
def sideTangent (u : ℝ × ℝ) : ℝ × ℝ := (-u.2, u.1)

/-- Side position and inward depth to physical coordinates. -/
def sideChart (u : ℝ × ℝ) (h : ℝ) (q : ℝ × ℝ) : ℝ × ℝ :=
  ((h - q.2) * u.1 - q.1 * u.2, (h - q.2) * u.2 + q.1 * u.1)

/-- Physical coordinates to side position and inward depth. -/
def sideCoords (u : ℝ × ℝ) (h : ℝ) (x : ℝ × ℝ) : ℝ × ℝ :=
  (dot x (sideTangent u), h - dot x u)

lemma sideCoords_chart (u : ℝ × ℝ) (hu : u.1 ^ 2 + u.2 ^ 2 = 1) (h : ℝ) (q : ℝ × ℝ) :
    sideCoords u h (sideChart u h q) = q := by
  apply Prod.ext <;> simp only [sideCoords, sideChart, sideTangent, dot]
  · nlinarith [congrArg (fun z : ℝ => q.1 * z) hu]
  · nlinarith [congrArg (fun z : ℝ => (h - q.2) * z) hu]

lemma sideChart_coords (u : ℝ × ℝ) (hu : u.1 ^ 2 + u.2 ^ 2 = 1) (h : ℝ) (x : ℝ × ℝ) :
    sideChart u h (sideCoords u h x) = x := by
  apply Prod.ext <;> simp only [sideCoords, sideChart, sideTangent, dot]
  · nlinarith [congrArg (fun z : ℝ => x.1 * z) hu]
  · nlinarith [congrArg (fun z : ℝ => x.2 * z) hu]

lemma continuous_sideChart (u : ℝ × ℝ) (h : ℝ) : Continuous (sideChart u h) := by
  unfold sideChart; fun_prop

lemma continuous_sideCoords (u : ℝ × ℝ) (h : ℝ) : Continuous (sideCoords u h) := by
  unfold sideCoords sideTangent dot; fun_prop

/-- The side chart as a measurable equivalence. -/
def sideEquiv (u : ℝ × ℝ) (hu : u.1 ^ 2 + u.2 ^ 2 = 1) (h : ℝ) :
    (ℝ × ℝ) ≃ᵐ (ℝ × ℝ) where
  toFun := sideChart u h
  invFun := sideCoords u h
  left_inv := sideCoords_chart u hu h
  right_inv := sideChart_coords u hu h
  measurable_toFun := (continuous_sideChart u h).measurable
  measurable_invFun := (continuous_sideCoords u h).measurable

/-- The side-coordinate Jacobian is exactly one. -/
theorem sideChart_preserving (u : ℝ × ℝ) (hu : u.1 ^ 2 + u.2 ^ 2 = 1) (h : ℝ) :
    MeasurePreserving (sideChart u h) volume volume := by
  let A : Matrix (Fin 2) (Fin 2) ℝ := !![-u.2, -u.1; u.1, -u.2]
  have hdet : A.det = 1 := by
    simp [Matrix.det_fin_two, A]
    nlinarith
  have hA : MeasurePreserving (Matrix.toLin' A) volume volume := by
    refine ⟨(LinearMap.continuous_on_pi _).measurable, ?_⟩
    rw [Real.map_matrix_volume_pi_eq_smul_volume_pi (by rw [hdet]; norm_num), hdet]
    simp
  let e := MeasurableEquiv.piFinTwo (fun _ : Fin 2 => ℝ)
  have he : MeasurePreserving e volume volume := volume_preserving_piFinTwo _
  have hlin := he.comp (hA.comp he.symm)
  have hadd := measurePreserving_add_left (volume : Measure (ℝ × ℝ)) (h * u.1, h * u.2)
  have hp := hadd.comp hlin
  convert hp using 1
  funext q
  apply Prod.ext <;>
    simp [sideChart, e, A, Matrix.toLin'_apply, Function.comp_def, MeasurableEquiv.piFinTwo] <;>
    ring

/-- Exact physical area of a rectangular position/depth window. -/
theorem sideChart_rectangle_volume (u : ℝ × ℝ) (hu : u.1 ^ 2 + u.2 ^ 2 = 1)
    (h a b d : ℝ) :
    volume (sideChart u h '' (Icc a b ×ˢ Icc 0 d)) =
      ENNReal.ofReal (b - a) * ENNReal.ofReal d := by
  let e := sideEquiv u hu h
  have hp : MeasurePreserving e volume volume := sideChart_preserving u hu h
  have he : e ⁻¹' (e '' (Icc a b ×ˢ Icc 0 d)) = Icc a b ×ˢ Icc 0 d :=
    e.injective.preimage_image _
  have hm : MeasurableSet (e '' (Icc a b ×ˢ Icc 0 d)) :=
    e.measurableEmbedding.measurableSet_image.2 (measurableSet_Icc.prod measurableSet_Icc)
  have hv := hp.measure_preimage hm.nullMeasurableSet
  rw [he, Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Icc, Real.volume_Icc,
    sub_zero] at hv
  exact hv.symm

end Enclosing
