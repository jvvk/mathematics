import EnclosingCopy.Enclosing.PolygonSampling

/-!
# Endpoint control for physical side strips

The neighbouring support lines bound the tangential projection of any polygon
point by the side interval enlarged by a constant times its inward depth.
This includes corner projections lying outside the original side interval.
-/
namespace Enclosing
open MeasureTheory Set
variable {m : ℕ} [NeZero m] {v : Fin m → ℝ × ℝ}

/-- Physical points with inward depth at most `d` from a supporting side. -/
def physicalSideStrip (K : Sides m) (i : Fin m) (d : ℝ) : Set (ℝ × ℝ) :=
  polygonRegion K ∩ {x | K.h i - dot x (K.u i) ∈ Icc 0 d}

omit [NeZero m] in
lemma measurableSet_physicalSideStrip (K : Sides m) (i : Fin m) (d : ℝ) :
    MeasurableSet (physicalSideStrip K i d) := by
  apply (measurableSet_polygonRegion K).inter
  exact measurableSet_Icc.preimage (by unfold dot; fun_prop)

/-- The forward neighbouring support line has positive slope along this side. -/
lemma next_side_slope_pos (hm : 3 ≤ m) (hv : ConvexPos v) (i : Fin m) :
    0 < dot (sideTangent (nrm v i)) (nrm v (i + 1)) := by
  have hL : aEnd v i < bEnd v i := by
    rw [← sub_pos, ← len_eq_b_sub_a v (nondeg_of_convex hm hv)]
    exact len_pos v (nondeg_of_convex hm hv) i
  have hA := hv (i + 1) i (Ne.symm (fin_add_one_ne hm i))
    (Ne.symm (fin_add_two_ne hm i))
  have hB : dot (v (i + 1)) (nrm v (i + 1)) = hsup v (i + 1) := rfl
  rw [← sideChart_start hm hv i, dot_sideChart_affine] at hA
  rw [← sideChart_end hm hv i, dot_sideChart_affine] at hB
  simp only [sub_zero] at hA hB
  by_contra h
  have hp := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hL.le) (le_of_not_gt h)
  nlinarith

/-- The backward neighbouring support line has negative slope along this side. -/
lemma prev_side_slope_neg (hm : 3 ≤ m) (hv : ConvexPos v) (i : Fin m) :
    dot (sideTangent (nrm v i)) (nrm v (i - 1)) < 0 := by
  have hprev : (i - 1) + 1 = i := sub_add_cancel i 1
  have hne : i - 1 ≠ i := by
    intro h
    rw [h] at hprev
    exact fin_add_one_ne hm i hprev
  have hL : aEnd v i < bEnd v i := by
    rw [← sub_pos, ← len_eq_b_sub_a v (nondeg_of_convex hm hv)]
    exact len_pos v (nondeg_of_convex hm hv) i
  have hA : dot (v i) (nrm v (i - 1)) = hsup v (i - 1) := by
    simpa only [hprev] using hsup_succ v (i - 1)
  have hB := hv (i - 1) (i + 1)
    (by intro h; have he := fin_add_two_ne hm (i - 1); rw [hprev] at he; exact he h)
    (by rw [hprev]; exact fin_add_one_ne hm i)
  rw [← sideChart_start hm hv i, dot_sideChart_affine] at hA
  rw [← sideChart_end hm hv i, dot_sideChart_affine] at hB
  simp only [sub_zero] at hA hB
  by_contra h
  have hp := mul_nonneg (sub_nonneg.mpr hL.le) (le_of_not_gt h)
  nlinarith

/-- Every physical strip fits in a side rectangle with only linear endpoint excess. -/
theorem exists_physicalSideStrip_enlargement (hm : 3 ≤ m) (hv : ConvexPos v)
    (harea : area v = 1) (i : Fin m) :
    let K := sidesOf v hm hv harea
    ∃ C ≥ 0, ∀ d ≥ 0, physicalSideStrip K i d ⊆
      sideWindow K i (K.a i - C * d) (K.b i + C * d) d := by
  intro K
  let R := dot (sideTangent (K.u i)) (K.u (i + 1))
  let L := -dot (sideTangent (K.u i)) (K.u (i - 1))
  let DR := dot (K.u i) (K.u (i + 1))
  let DL := dot (K.u i) (K.u (i - 1))
  have hR : 0 < R := next_side_slope_pos hm hv i
  have hL : 0 < L := neg_pos.mpr (prev_side_slope_neg hm hv i)
  let C := |DR| / R + |DL| / L
  have hCR : 0 ≤ |DR| / R := div_nonneg (abs_nonneg _) hR.le
  have hCL : 0 ≤ |DL| / L := div_nonneg (abs_nonneg _) hL.le
  refine ⟨C, add_nonneg hCR hCL, ?_⟩
  intro d hd x hx
  let q := sideCoords (K.u i) (K.h i) x
  have hq : sideChart (K.u i) (K.h i) q = x :=
    sideChart_coords _ ((goodSides_of_convex hm hv harea).unit i) _ x
  have hdepth : q.2 ∈ Icc 0 d := hx.2
  have hb0 : K.h i * DR + K.b i * R = K.h (i + 1) := by
    have he : dot (v (i + 1)) (K.u (i + 1)) = K.h (i + 1) := rfl
    rw [← sideChart_end hm hv i, dot_sideChart_affine] at he
    simpa only [sub_zero, K, sidesOf, DR, R] using he
  have ha0 : K.h i * DL - K.a i * L = K.h (i - 1) := by
    have he : dot (v i) (K.u (i - 1)) = K.h (i - 1) := by
      simpa only [sub_add_cancel, K, sidesOf] using hsup_succ v (i - 1)
    rw [← sideChart_start hm hv i, dot_sideChart_affine] at he
    dsimp [L, DL]
    simpa only [sub_zero, mul_neg, sub_neg_eq_add, K, sidesOf] using he
  have hright := hx.1 (i + 1)
  have hleft := hx.1 (i - 1)
  rw [← hq, dot_sideChart_affine] at hright hleft
  have hRD : q.2 * DR ≤ d * |DR| :=
    (mul_le_mul_of_nonneg_left (le_abs_self DR) hdepth.1).trans
      (mul_le_mul_of_nonneg_right hdepth.2 (abs_nonneg _))
  have hLD : q.2 * DL ≤ d * |DL| :=
    (mul_le_mul_of_nonneg_left (le_abs_self DL) hdepth.1).trans
      (mul_le_mul_of_nonneg_right hdepth.2 (abs_nonneg _))
  have hright' : q.1 - K.b i ≤ d * (|DR| / R) := by
    rw [← mul_div_assoc]
    apply (le_div_iff₀ hR).mpr
    dsimp [R, DR] at *
    nlinarith
  have hleft' : K.a i - q.1 ≤ d * (|DL| / L) := by
    rw [← mul_div_assoc]
    apply (le_div_iff₀ hL).mpr
    dsimp [L, DL] at *
    nlinarith
  refine ⟨q, ⟨⟨?_, ?_⟩, hdepth⟩, hq⟩
  · have hle := mul_le_mul_of_nonneg_left (show |DL| / L ≤ C by dsimp [C]; linarith) hd
    nlinarith
  · have hle := mul_le_mul_of_nonneg_left (show |DR| / R ≤ C by dsimp [C]; linarith) hd
    nlinarith

end Enclosing
