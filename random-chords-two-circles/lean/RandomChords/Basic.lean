import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Random chords of two circles (MO 499477): the model

Angles live on the circle `Ang = ℝ ⧸ 2πℤ` with its Haar measure (total mass `2π`), so a uniform
point of a circle is `centre + r (cos α, sin α)` for `α` distributed by `volume / (2π)`. Laws are
compared as push-forwards of `volume` on `Ang × Ang`; equality of these is equality in distribution.

The line through two distinct points `X, Y` has the unit normal `nrm X Y`, with the sign chosen so that
its second coordinate is non-negative (the paper's `m = (cos φ, sin φ)`, `0 < φ < π`; vertical lines
get one of the two normals, a null event). The signed offset of the line from a centre `Z`, in units
of the radius `r`, is `offset X Y Z r = m · (X - Z) / r`. `lineDist O X Y` is the Euclidean distance
from `O` to the line `XY`.
-/

open Real MeasureTheory Set

noncomputable section

namespace Chords

instance fact_two_pi_pos : Fact (0 < 2 * π) := ⟨by positivity⟩

/-- Angles modulo `2π`. -/
abbrev Ang := AddCircle (2 * π)

/-- Cosine and sine of an angle modulo `2π`. -/
def ccos : Ang → ℝ := Real.cos_periodic.lift
def csin : Ang → ℝ := Real.sin_periodic.lift

@[simp] lemma ccos_coe (x : ℝ) : ccos (x : Ang) = Real.cos x := rfl
@[simp] lemma csin_coe (x : ℝ) : csin (x : Ang) = Real.sin x := rfl

@[fun_prop] lemma continuous_ccos : Continuous ccos :=
  continuous_quot_lift _ Real.continuous_cos
@[fun_prop] lemma continuous_csin : Continuous csin :=
  continuous_quot_lift _ Real.continuous_sin

lemma measurable_ccos : Measurable ccos := continuous_ccos.measurable
lemma measurable_csin : Measurable csin := continuous_csin.measurable

/-- The point at angle `α` on the circle of radius `r` about `(c, 0)`. -/
def pt (c r : ℝ) (α : Ang) : ℝ × ℝ := (c + r * ccos α, r * csin α)

@[fun_prop] lemma continuous_pt (c r : ℝ) : Continuous (pt c r) := by unfold pt; fun_prop

/-- Euclidean length of a plane vector. -/
def len (v : ℝ × ℝ) : ℝ := √(v.1 ^ 2 + v.2 ^ 2)

/-- The sign that makes the normal's second coordinate non-negative. -/
def sgn (d : ℝ × ℝ) : ℝ := if 0 < d.1 then 1 else -1

/-- The unit normal of a line with direction `d`, with non-negative second coordinate. -/
def nrmD (d : ℝ × ℝ) : ℝ × ℝ := (sgn d * -d.2 / len d, sgn d * d.1 / len d)

/-- The unit normal of the line through `X` and `Y`. -/
def nrm (X Y : ℝ × ℝ) : ℝ × ℝ := nrmD (Y - X)

/-- Signed offset `m · (X - Z) / r` of a line with normal `m` through `X` from the centre `Z`. -/
def off (m X Z : ℝ × ℝ) (r : ℝ) : ℝ := (m.1 * (X.1 - Z.1) + m.2 * (X.2 - Z.2)) / r

/-- The Euclidean distance from `O` to the line through `X` and `Y`. -/
def lineDist (O X Y : ℝ × ℝ) : ℝ :=
  |(Y.1 - X.1) * (O.2 - X.2) - (Y.2 - X.2) * (O.1 - X.1)| / len (Y - X)

/-- Two circles: radius `a` about `P = (-D, 0)` and radius `b` about `Q = (0, 0)`. For `A` and `B`
at angles `ω`, the angles `θ_A, θ_B ∈ [0, π]` between the normal of `AB` and the radii to `A`, `B`
(so `x_A = cos θ_A`, `x_B = cos θ_B`). -/
def angles2 (a b D : ℝ) (ω : Ang × Ang) : ℝ × ℝ :=
  (arccos (off (nrm (pt (-D) a ω.1) (pt 0 b ω.2)) (pt (-D) a ω.1) (-D, 0) a),
   arccos (off (nrm (pt (-D) a ω.1) (pt 0 b ω.2)) (pt 0 b ω.2) (0, 0) b))

/-- One circle: radius `b` about `(0, 0)`. For the chord `BC`, the normal angle `φ ∈ [0, π]`
(`m = (cos φ, sin φ)`) and the angle `θ_B` between `m` and the radius to `B`. -/
def angles1 (b : ℝ) (ω : Ang × Ang) : ℝ × ℝ :=
  (arccos (nrm (pt 0 b ω.1) (pt 0 b ω.2)).1,
   arccos (off (nrm (pt 0 b ω.1) (pt 0 b ω.2)) (pt 0 b ω.1) (0, 0) b))

/-- The open square `(0, π)²` of angle pairs. -/
def sq : Set (ℝ × ℝ) := Ioo 0 π ×ˢ Ioo 0 π

lemma measurableSet_sq : MeasurableSet sq := measurableSet_Ioo.prod measurableSet_Ioo

lemma volume_sq : volume sq = ENNReal.ofReal π * ENNReal.ofReal π := by
  rw [sq, Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Ioo, sub_zero]

lemma volume_univ_ang2 :
    volume (univ : Set (Ang × Ang)) = ENNReal.ofReal (2 * π) * ENNReal.ofReal (2 * π) := by
  rw [← univ_prod_univ, Measure.volume_eq_prod, Measure.prod_prod, AddCircle.measure_univ]

/-- The total mass of `Ang × Ang` is four times the area of the square `(0, π)²`. -/
lemma four_mul_volume_sq : 4 * volume sq = volume (univ : Set (Ang × Ang)) := by
  rw [volume_sq, volume_univ_ang2, ← ENNReal.ofReal_mul pi_pos.le,
    ← ENNReal.ofReal_mul (by positivity), show (4 : ENNReal) = ENNReal.ofReal 4 by norm_num,
    ← ENNReal.ofReal_mul (by norm_num)]
  congr 1; ring

/-- The determinant of a linear map of the plane, from its matrix. -/
lemma det_two (p q r s : ℝ) :
    ((p • ContinuousLinearMap.fst ℝ ℝ ℝ + q • ContinuousLinearMap.snd ℝ ℝ ℝ).prod
      (r • ContinuousLinearMap.fst ℝ ℝ ℝ + s • ContinuousLinearMap.snd ℝ ℝ ℝ)).det =
      p * s - q * r := by
  rw [ContinuousLinearMap.det, ← LinearMap.det_toMatrix (Module.Basis.finTwoProd ℝ),
    Matrix.det_fin_two]
  simp [LinearMap.toMatrix_apply]

lemma len_smul (l φ : ℝ) : len (l * sin φ, -(l * cos φ)) = |l| := by
  unfold len
  rw [show (l * sin φ) ^ 2 + (-(l * cos φ)) ^ 2 = l ^ 2 * (sin φ ^ 2 + cos φ ^ 2) by ring,
    sin_sq_add_cos_sq, mul_one, Real.sqrt_sq_eq_abs]

/-- A line with direction `l (sin φ, -cos φ)`, `l ≠ 0`, `0 < φ < π`, has normal `(cos φ, sin φ)`. -/
lemma nrmD_eq {l φ : ℝ} (hl : l ≠ 0) (hφ : 0 < sin φ) :
    nrmD (l * sin φ, -(l * cos φ)) = (cos φ, sin φ) := by
  unfold nrmD sgn
  rw [len_smul]
  rcases lt_or_gt_of_ne hl with h | h
  · have h1 : ¬ (0 < l * sin φ) := by nlinarith
    simp only [h1, ite_false, abs_of_neg h]
    refine Prod.ext ?_ ?_ <;> field_simp
  · have h1 : 0 < l * sin φ := by positivity
    simp only [h1, ite_true, abs_of_pos h]
    refine Prod.ext ?_ ?_ <;> field_simp

/-- The offset of the line with normal `(cos φ, sin φ)` through the point at angle `x` of the circle
of radius `r` about `(c, 0)` is `cos (x - φ)`. -/
lemma off_pt (c r φ x : ℝ) (hr : r ≠ 0) :
    off (cos φ, sin φ) (pt c r (x : Ang)) (c, 0) r = cos (x - φ) := by
  unfold off pt
  simp only [ccos_coe, csin_coe, add_sub_cancel_left, sub_zero, cos_sub]
  field_simp

lemma measurable_sgn : Measurable sgn :=
  Measurable.ite (measurableSet_lt measurable_const measurable_fst) measurable_const measurable_const

lemma measurable_len : Measurable len := by unfold len; fun_prop

lemma measurable_nrmD : Measurable nrmD :=
  Measurable.prodMk ((measurable_sgn.mul measurable_snd.neg).div measurable_len)
    ((measurable_sgn.mul measurable_fst).div measurable_len)

lemma measurable_angles2 (a b D : ℝ) : Measurable (angles2 a b D) := by
  have hA : Measurable (fun ω : Ang × Ang => pt (-D) a ω.1) := (continuous_pt _ _).measurable.comp measurable_fst
  have hB : Measurable (fun ω : Ang × Ang => pt 0 b ω.2) := (continuous_pt _ _).measurable.comp measurable_snd
  have hm : Measurable (fun ω : Ang × Ang => nrm (pt (-D) a ω.1) (pt 0 b ω.2)) :=
    measurable_nrmD.comp (hB.sub hA)
  unfold angles2 off
  refine Measurable.prodMk (continuous_arccos.measurable.comp ?_) (continuous_arccos.measurable.comp ?_)
  · exact (((hm.fst.mul (hA.fst.sub measurable_const)).add
      (hm.snd.mul (hA.snd.sub measurable_const))).div_const _)
  · exact (((hm.fst.mul (hB.fst.sub measurable_const)).add
      (hm.snd.mul (hB.snd.sub measurable_const))).div_const _)

lemma measurable_angles1 (b : ℝ) : Measurable (angles1 b) := by
  have hB : Measurable (fun ω : Ang × Ang => pt 0 b ω.1) := (continuous_pt _ _).measurable.comp measurable_fst
  have hC : Measurable (fun ω : Ang × Ang => pt 0 b ω.2) := (continuous_pt _ _).measurable.comp measurable_snd
  have hm : Measurable (fun ω : Ang × Ang => nrm (pt 0 b ω.1) (pt 0 b ω.2)) :=
    measurable_nrmD.comp (hC.sub hB)
  unfold angles1 off
  refine Measurable.prodMk (continuous_arccos.measurable.comp hm.fst)
    (continuous_arccos.measurable.comp ?_)
  exact (((hm.fst.mul (hB.fst.sub measurable_const)).add
      (hm.snd.mul (hB.snd.sub measurable_const))).div_const _)

end Chords
