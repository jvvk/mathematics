import Mathlib.Analysis.Normed.Affine.AddTorsorBases
import Mathlib.Analysis.Convex.Combination
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Tetrahedra: volume and the origin in the interior

Corollary 3 writes the vertex term with `Vol(T) 1{0 ∈ int T}` for a tetrahedron `T` with vertices
`P₀, …, P₃ ∈ ℝ³`, while the cone density of Theorem 8 is written with the determinant of the
homogeneous matrix `M` with rows `(1, P_r)` and positive barycentric weights. They agree
(`tetW_eq`):

* if `det M = 0`, the points lie in a plane `a + n · x = 0` with `n ≠ 0`, so `T` has empty
  interior and both sides vanish;
* if `det M ≠ 0`, the points form an affine basis; the interior of `T` is the set of points with
  positive barycentric coordinates (`AffineBasis.interior_convexHull`), and `T` is the image of
  the corner simplex `{y ≥ 0, ∑ y ≤ 1}`, of volume `1/6`, under an affine map of determinant
  `det M`.
-/

namespace Enclosing

open MeasureTheory Set
open scoped Matrix

/-- Points of `ℝ³`. -/
abbrev R3 := Fin 3 → ℝ

/-- The homogeneous matrix with rows `(1, P r)`. -/
def homMat (P : Fin 4 → R3) : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.of fun r => ![1, P r 0, P r 1, P r 2]

/-- The origin is a combination of the points with positive weights summing to one. -/
def PosBary (P : Fin 4 → R3) : Prop :=
  ∃ l : Fin 4 → ℝ, (∀ r, 0 < l r) ∧ ∑ r, l r = 1 ∧ ∑ r, l r • P r = 0

/-- The tetrahedron spanned by four points. -/
def tet (P : Fin 4 → R3) : Set R3 := convexHull ℝ (range P)

/-- `Vol(T) 1{0 ∈ int T}`. -/
noncomputable def tetW (P : Fin 4 → R3) : ENNReal :=
  volume (tet P) * {P : Fin 4 → R3 | (0 : R3) ∈ interior (tet P)}.indicator 1 P

/-! ### The degenerate case -/

lemma interior_tet_empty {P : Fin 4 → R3} (h : (homMat P).det = 0) : interior (tet P) = ∅ := by
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h
  have hrow : ∀ r, v 0 + (v 1 * P r 0 + v 2 * P r 1 + v 3 * P r 2) = 0 := by
    intro r
    have := congr_fun hv r
    simp [Matrix.mulVec, dotProduct, homMat, Fin.sum_univ_four, Matrix.vecHead,
      Matrix.vecTail] at this
    linarith
  have hn : v 1 ≠ 0 ∨ v 2 ≠ 0 ∨ v 3 ≠ 0 := by
    by_contra hc
    push Not at hc
    obtain ⟨h1, h2, h3⟩ := hc
    have h0 : v 0 = 0 := by have := hrow 0; rw [h1, h2, h3] at this; linarith
    apply hv0
    funext i
    fin_cases i <;> simp [h0, h1, h2, h3]
  set H : Set R3 := {x | v 0 + (v 1 * x 0 + v 2 * x 1 + v 3 * x 2) = 0}
  have hHc : Convex ℝ H := by
    intro x hx y hy a b _ _ hab
    simp only [H, mem_setOf_eq, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hx hy ⊢
    linear_combination a * hx + b * hy - v 0 * hab
  have hsub : tet P ⊆ H := convexHull_min (by rintro _ ⟨r, rfl⟩; exact hrow r) hHc
  have hN : 0 < v 1 * v 1 + v 2 * v 2 + v 3 * v 3 := by
    rcases hn with h | h | h
    · have := mul_self_pos.2 h; nlinarith [mul_self_nonneg (v 2), mul_self_nonneg (v 3)]
    · have := mul_self_pos.2 h; nlinarith [mul_self_nonneg (v 1), mul_self_nonneg (v 3)]
    · have := mul_self_pos.2 h; nlinarith [mul_self_nonneg (v 1), mul_self_nonneg (v 2)]
  rw [eq_empty_iff_forall_notMem]
  intro x hx
  have hxH := interior_mono hsub hx
  rw [mem_interior_iff_mem_nhds, Metric.mem_nhds_iff] at hxH
  obtain ⟨ε, hε, hball⟩ := hxH
  set n : R3 := ![v 1, v 2, v 3]
  set δ := ε / (2 * (‖n‖ + 1))
  have hδ : 0 < δ := by positivity
  have hy : x + δ • n ∈ Metric.ball x ε := by
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hδ.le]
    have h1 : δ * ‖n‖ ≤ δ * (‖n‖ + 1) := by nlinarith [norm_nonneg n]
    have h2 : δ * (‖n‖ + 1) = ε / 2 := by
      simp only [δ]; field_simp
    linarith
  have h1 := hball hy
  have h0 := hball (Metric.mem_ball_self hε)
  simp [H, n, Matrix.vecHead, Matrix.vecTail] at h1 h0
  have : δ * (v 1 * v 1 + v 2 * v 2 + v 3 * v 3) = 0 := by linear_combination h1 - h0
  rcases mul_eq_zero.1 this with h | h
  · exact hδ.ne' h
  · exact hN.ne' h

/-! ### The nondegenerate case: an affine basis -/

lemma affInd_of_det {P : Fin 4 → R3} (h : (homMat P).det ≠ 0) : AffineIndependent ℝ P := by
  rw [affineIndependent_iff_of_fintype]
  intro w hw hs
  rw [Finset.weightedVSub_eq_linear_combination _ hw] at hs
  have hv : w ᵥ* homMat P = 0 := by
    funext c
    have hj : ∀ j, ∑ r, w r * P r j = 0 := fun j => by
      have := congr_fun hs j
      simpa [Finset.sum_apply] using this
    fin_cases c
    · simpa [Matrix.vecMul, dotProduct, homMat] using hw
    · simpa [Matrix.vecMul, dotProduct, homMat] using hj 0
    · simpa [Matrix.vecMul, dotProduct, homMat] using hj 1
    · simpa [Matrix.vecMul, dotProduct, homMat] using hj 2
  intro i
  exact congr_fun (Matrix.eq_zero_of_vecMul_eq_zero h hv) i

/-- The vertices of a nondegenerate tetrahedron as an affine basis. -/
noncomputable def tetBasis {P : Fin 4 → R3} (h : (homMat P).det ≠ 0) : AffineBasis (Fin 4) ℝ R3 :=
  ⟨P, affInd_of_det h, by
    rw [(affInd_of_det h).affineSpan_eq_top_iff_card_eq_finrank_add_one]
    simp⟩

lemma tetBasis_coe {P : Fin 4 → R3} (h : (homMat P).det ≠ 0) : ⇑(tetBasis h) = P := rfl

lemma zero_mem_interior_iff {P : Fin 4 → R3} (h : (homMat P).det ≠ 0) :
    (0 : R3) ∈ interior (tet P) ↔ PosBary P := by
  set b := tetBasis h
  rw [tet, ← tetBasis_coe h, b.interior_convexHull, mem_setOf_eq]
  constructor
  · intro hpos
    exact ⟨fun i => b.coord i 0, hpos, b.sum_coord_apply_eq_one 0,
      b.linear_combination_coord_eq_self 0⟩
  · rintro ⟨l, hl, h1, h0⟩ i
    have hc : Finset.univ.affineCombination ℝ b l = 0 := by
      rw [Finset.affineCombination_eq_linear_combination _ _ _ h1]
      exact h0
    rw [← hc, b.coord_apply_combination_of_mem (Finset.mem_univ i) h1]
    exact hl i

/-! ### The volume -/

/-- The corner simplex `{y ≥ 0, ∑ y ≤ 1}`. -/
def corner : Set R3 := {y | (∀ i, 0 ≤ y i) ∧ ∑ i, y i ≤ 1}

/-- The edge matrix: column `i` is `P (i+1) - P 0`. -/
def edgeMat (P : Fin 4 → R3) : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.of fun j i => P i.succ j - P 0 j

lemma det_edgeMat (P : Fin 4 → R3) : (edgeMat P).det = (homMat P).det := by
  simp only [edgeMat, homMat, Matrix.det_fin_three, Matrix.det_succ_row_zero, Fin.sum_univ_succ,
    Matrix.of_apply, Matrix.submatrix_apply, Fin.succ_zero_eq_one, Fin.succ_one_eq_two]
  simp [Fin.succAbove, Fin.lt_def, Matrix.det_fin_three]
  ring

lemma tet_eq_image {P : Fin 4 → R3} (h : (homMat P).det ≠ 0) :
    tet P = (fun y => P 0 + Matrix.toLin' (edgeMat P) y) '' corner := by
  set b := tetBasis h
  have hcoe := tetBasis_coe h
  rw [tet, ← hcoe, b.convexHull_eq_nonneg_coord, hcoe]
  ext x
  simp only [mem_setOf_eq, mem_image, corner, Matrix.toLin'_apply]
  constructor
  · intro hx
    refine ⟨fun i => b.coord i.succ x, ⟨fun i => hx _, ?_⟩, ?_⟩
    · have := b.sum_coord_apply_eq_one x
      rw [Fin.sum_univ_succ] at this
      linarith [hx 0]
    · have hs := b.sum_coord_apply_eq_one x
      have hl := b.linear_combination_coord_eq_self x
      rw [hcoe] at hl
      funext j
      have hj := congr_fun hl j
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Fin.sum_univ_four] at hj
      simp only [Fin.sum_univ_four] at hs
      simp only [Pi.add_apply, Matrix.mulVec, dotProduct, edgeMat, Matrix.of_apply,
        Fin.sum_univ_three]
      simp only [Fin.succ_zero_eq_one, Fin.succ_one_eq_two]
      rw [show (Fin.succ (2 : Fin 3) : Fin 4) = 3 from rfl]
      linear_combination hj - P 0 j * hs
  · rintro ⟨y, ⟨hy0, hy1⟩, rfl⟩
    set l : Fin 4 → ℝ := ![1 - (y 0 + y 1 + y 2), y 0, y 1, y 2]
    have hl1 : ∑ r, l r = 1 := by simp [l, Fin.sum_univ_four]; ring
    have hcomb : P 0 + (edgeMat P) *ᵥ y = Finset.univ.affineCombination ℝ b l := by
      rw [Finset.affineCombination_eq_linear_combination _ _ _ hl1, hcoe]
      funext j
      simp only [Pi.add_apply, Matrix.mulVec, dotProduct, edgeMat, Matrix.of_apply,
        Fin.sum_univ_three, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Fin.sum_univ_four, l]
      simp only [Fin.succ_zero_eq_one, Fin.succ_one_eq_two]
      rw [show (Fin.succ (2 : Fin 3) : Fin 4) = 3 from rfl]
      simp
      ring
    intro i
    rw [hcomb, b.coord_apply_combination_of_mem (Finset.mem_univ i) hl1]
    have hs : ∑ i, y i = y 0 + y 1 + y 2 := Fin.sum_univ_three y
    fin_cases i
    · simp [l]; linarith
    · simp [l]; exact hy0 0
    · simp [l]; exact hy0 1
    · simp [l]; exact hy0 2

/-- `∫⁻_{y ≥ 0} (a - y)₊ dy = (a₊)²/2`. -/
lemma lintegral_tent (a : ℝ) :
    ∫⁻ y in Ici (0 : ℝ), ENNReal.ofReal (a - y) = ENNReal.ofReal (max a 0 ^ 2 / 2) := by
  rcases le_or_gt a 0 with ha | ha
  · rw [max_eq_right ha]
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_div,
      ENNReal.ofReal_zero]
    rw [← lintegral_indicator measurableSet_Ici]
    refine (lintegral_congr fun y => ?_).trans lintegral_zero
    by_cases hy : y ∈ Ici (0 : ℝ)
    · rw [indicator_of_mem hy, ENNReal.ofReal_of_nonpos (by have : (0 : ℝ) ≤ y := hy; linarith)]
    · rw [indicator_of_notMem hy]
  · rw [max_eq_left ha.le, ← lintegral_indicator measurableSet_Ici]
    have he : (Ici (0 : ℝ)).indicator (fun y => ENNReal.ofReal (a - y)) =
        (Icc 0 a).indicator (fun y => ENNReal.ofReal (a - y)) := by
      funext y
      by_cases h0 : 0 ≤ y
      · by_cases h1 : y ≤ a
        · rw [indicator_of_mem (show y ∈ Ici (0 : ℝ) from h0),
            indicator_of_mem (show y ∈ Icc 0 a from ⟨h0, h1⟩)]
        · rw [indicator_of_mem (show y ∈ Ici (0 : ℝ) from h0),
            indicator_of_notMem (show y ∉ Icc 0 a from fun h => h1 h.2),
            ENNReal.ofReal_of_nonpos (by linarith)]
      · rw [indicator_of_notMem (show y ∉ Ici (0 : ℝ) from h0),
          indicator_of_notMem (show y ∉ Icc 0 a from fun h => h0 h.1)]
    rw [he, lintegral_indicator measurableSet_Icc,
      ← ofReal_integral_eq_lintegral_ofReal
        ((by fun_prop : Continuous fun y : ℝ => a - y).integrableOn_Icc)
        ((ae_restrict_iff' measurableSet_Icc).2 (Filter.Eventually.of_forall fun y hy => by
          have := hy.2; simp only [Pi.zero_apply]; linarith)),
      integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le ha.le]
    have hi : ∫ y in (0 : ℝ)..a, (a - y) = a ^ 2 / 2 := by
      rw [intervalIntegral.integral_sub intervalIntegrable_const
        intervalIntegral.intervalIntegrable_id, integral_id, intervalIntegral.integral_const]
      simp; ring
    rw [hi]

lemma volume_corner : volume corner = ENNReal.ofReal (1 / 6) := by
  let S : Set (ℝ × ℝ × ℝ) := {p | 0 ≤ p.1 ∧ 0 ≤ p.2.1 ∧ 0 ≤ p.2.2 ∧ p.1 + p.2.1 + p.2.2 ≤ 1}
  have hS : MeasurableSet S := by
    refine (measurableSet_le measurable_const measurable_fst).inter
      ((measurableSet_le measurable_const measurable_snd.fst).inter
        ((measurableSet_le measurable_const measurable_snd.snd).inter
          (measurableSet_le (f := fun p : ℝ × ℝ × ℝ => p.1 + p.2.1 + p.2.2) (by fun_prop)
            measurable_const)))
  have hmp : MeasurePreserving (fun y : R3 => (y 0, y 1, y 2))
      (volume : Measure R3) ((volume : Measure ℝ).prod ((volume : Measure ℝ).prod volume)) := by
    have h := ((MeasurePreserving.id (volume : Measure ℝ)).prod
      (measurePreserving_finTwoArrow (volume : Measure ℝ))).comp
      (measurePreserving_piFinSuccAbove (fun _ : Fin 3 => (volume : Measure ℝ)) 0)
    rw [← volume_pi] at h
    convert h using 1
    funext y
    rfl
  have hpre : corner = (fun y : R3 => (y 0, y 1, y 2)) ⁻¹' S := by
    ext y
    simp only [corner, S, mem_setOf_eq, mem_preimage, Fin.forall_fin_succ, Fin.sum_univ_three,
      IsEmpty.forall_iff, and_true]
    simp only [Fin.succ_zero_eq_one, Fin.succ_one_eq_two]
    tauto
  rw [hpre, hmp.measure_preimage hS.nullMeasurableSet, Measure.prod_apply hS]
  -- innermost: the `z`-slice
  have hz : ∀ x y : ℝ, volume {z : ℝ | (x, y, z) ∈ S} =
      {p : ℝ × ℝ | 0 ≤ p.1 ∧ 0 ≤ p.2}.indicator (fun p => ENNReal.ofReal (1 - p.1 - p.2)) (x, y) := by
    intro x y
    by_cases hxy : 0 ≤ x ∧ 0 ≤ y
    · rw [indicator_of_mem (show (x, y) ∈ {p : ℝ × ℝ | 0 ≤ p.1 ∧ 0 ≤ p.2} from hxy)]
      have : {z : ℝ | (x, y, z) ∈ S} = Icc 0 (1 - x - y) := by
        ext z; simp only [S, mem_setOf_eq, mem_Icc]
        constructor
        · rintro ⟨-, -, h1, h2⟩; exact ⟨h1, by linarith⟩
        · rintro ⟨h1, h2⟩; exact ⟨hxy.1, hxy.2, h1, by linarith⟩
      rw [this, Real.volume_Icc, sub_zero]
    · rw [indicator_of_notMem (show (x, y) ∉ {p : ℝ × ℝ | 0 ≤ p.1 ∧ 0 ≤ p.2} from hxy)]
      have : {z : ℝ | (x, y, z) ∈ S} = ∅ := by
        ext z; simp only [S, mem_setOf_eq, mem_empty_iff_false, iff_false]
        rintro ⟨h1, h2, -, -⟩; exact hxy ⟨h1, h2⟩
      rw [this, measure_empty]
  -- middle: the `(y, z)`-slice
  have hyz : ∀ x : ℝ, ((volume : Measure ℝ).prod volume) (Prod.mk x ⁻¹' S) =
      (Ici (0 : ℝ)).indicator (fun x => ENNReal.ofReal (max (1 - x) 0 ^ 2 / 2)) x := by
    intro x
    have hSx : MeasurableSet (Prod.mk x ⁻¹' S) := measurable_prodMk_left hS
    rw [Measure.prod_apply hSx]
    have hz' : ∀ y, volume (Prod.mk y ⁻¹' (Prod.mk x ⁻¹' S)) =
        {p : ℝ × ℝ | 0 ≤ p.1 ∧ 0 ≤ p.2}.indicator (fun p => ENNReal.ofReal (1 - p.1 - p.2)) (x, y) :=
      hz x
    simp_rw [hz']
    by_cases hx : 0 ≤ x
    · rw [indicator_of_mem (show x ∈ Ici (0 : ℝ) from hx), ← lintegral_tent,
        ← lintegral_indicator measurableSet_Ici]
      refine lintegral_congr fun y => ?_
      by_cases hy : 0 ≤ y
      · rw [indicator_of_mem (show (x, y) ∈ {p : ℝ × ℝ | 0 ≤ p.1 ∧ 0 ≤ p.2} from ⟨hx, hy⟩),
          indicator_of_mem (show y ∈ Ici (0 : ℝ) from hy)]
      · rw [indicator_of_notMem (show (x, y) ∉ {p : ℝ × ℝ | 0 ≤ p.1 ∧ 0 ≤ p.2} from
          fun h => hy h.2), indicator_of_notMem (show y ∉ Ici (0 : ℝ) from hy)]
    · rw [indicator_of_notMem (show x ∉ Ici (0 : ℝ) from hx)]
      refine (lintegral_congr fun y => ?_).trans lintegral_zero
      rw [indicator_of_notMem (show (x, y) ∉ {p : ℝ × ℝ | 0 ≤ p.1 ∧ 0 ≤ p.2} from
        fun h => hx h.1)]
  simp_rw [hyz]
  rw [lintegral_indicator measurableSet_Ici]
  -- outer: `∫_{x ≥ 0} (1 - x)₊² / 2 = 1/6`
  have he : ∀ x ∈ Ici (0 : ℝ), ENNReal.ofReal (max (1 - x) 0 ^ 2 / 2) =
      (Icc (0 : ℝ) 1).indicator (fun x => ENNReal.ofReal ((1 - x) ^ 2 / 2)) x := by
    intro x hx
    by_cases h1 : x ≤ 1
    · rw [indicator_of_mem (show x ∈ Icc (0 : ℝ) 1 from ⟨hx, h1⟩), max_eq_left (by linarith)]
    · rw [indicator_of_notMem (show x ∉ Icc (0 : ℝ) 1 from fun h => h1 h.2),
        max_eq_right (by linarith)]
      simp
  rw [setLIntegral_congr_fun measurableSet_Ici he, ← lintegral_indicator measurableSet_Ici]
  have he2 : (Ici (0 : ℝ)).indicator (fun x => (Icc (0 : ℝ) 1).indicator
      (fun x => ENNReal.ofReal ((1 - x) ^ 2 / 2)) x) =
      (Icc (0 : ℝ) 1).indicator (fun x => ENNReal.ofReal ((1 - x) ^ 2 / 2)) := by
    funext x
    by_cases h : x ∈ Icc (0 : ℝ) 1
    · rw [indicator_of_mem (show x ∈ Ici (0 : ℝ) from h.1)]
    · by_cases h0 : x ∈ Ici (0 : ℝ)
      · rw [indicator_of_mem h0]
      · rw [indicator_of_notMem h0, indicator_of_notMem h]
  rw [he2, lintegral_indicator measurableSet_Icc,
    ← ofReal_integral_eq_lintegral_ofReal (by fun_prop : Continuous fun x : ℝ => (1 - x) ^ 2 / 2).integrableOn_Icc
      (Filter.Eventually.of_forall fun x => by positivity),
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one]
  congr 1
  rw [intervalIntegral.integral_div, intervalIntegral.integral_comp_sub_left (fun x => x ^ 2)]
  norm_num [integral_pow]

lemma volume_tet {P : Fin 4 → R3} (h : (homMat P).det ≠ 0) :
    volume (tet P) = ENNReal.ofReal (|(homMat P).det| / 6) := by
  rw [tet_eq_image h, show (fun y => P 0 + Matrix.toLin' (edgeMat P) y) =
      (fun x => P 0 + x) ∘ Matrix.toLin' (edgeMat P) from rfl, image_comp, image_add_left,
    measure_preimage_add, Measure.addHaar_image_linearMap, LinearMap.det_toLin', det_edgeMat,
    volume_corner, ← ENNReal.ofReal_mul (abs_nonneg _)]
  congr 1; ring

/-- **`Vol(T) 1{0 ∈ int T} = |det M|/6 · 1{0 is a positive combination}`.** -/
theorem tetW_eq (P : Fin 4 → R3) :
    tetW P = ENNReal.ofReal ({P : Fin 4 → R3 | PosBary P}.indicator
      (fun P => |(homMat P).det| / 6) P) := by
  unfold tetW
  by_cases h : (homMat P).det = 0
  · rw [indicator_of_notMem (show P ∉ {P : Fin 4 → R3 | (0 : R3) ∈ interior (tet P)} by
      simp [interior_tet_empty h]), mul_zero]
    by_cases hp : PosBary P
    · rw [indicator_of_mem (show P ∈ {P : Fin 4 → R3 | PosBary P} from hp), h]; simp
    · rw [indicator_of_notMem (show P ∉ {P : Fin 4 → R3 | PosBary P} from hp)]; simp
  · rw [volume_tet h]
    by_cases hp : PosBary P
    · rw [indicator_of_mem (show P ∈ {P : Fin 4 → R3 | PosBary P} from hp),
        indicator_of_mem (show P ∈ {P : Fin 4 → R3 | (0 : R3) ∈ interior (tet P)} from
          (zero_mem_interior_iff h).2 hp)]
      simp
    · rw [indicator_of_notMem (show P ∉ {P : Fin 4 → R3 | PosBary P} from hp),
        indicator_of_notMem (show P ∉ {P : Fin 4 → R3 | (0 : R3) ∈ interior (tet P)} from
          fun h' => hp ((zero_mem_interior_iff h).1 h'))]
      simp

end Enclosing
