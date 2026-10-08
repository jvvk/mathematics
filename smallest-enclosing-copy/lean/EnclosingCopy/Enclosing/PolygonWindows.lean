import EnclosingCopy.Enclosing.PolygonRegion

/-!
# Trimmed side rectangles lie inside a genuine convex polygon

Strict convex position provides positive slack at every interior point of a side,
relative to every other supporting line. Compact trimmed subintervals therefore have
a common positive admissible depth. The side chart supplies their exact area.
-/
namespace Enclosing
open MeasureTheory Set Filter Topology
variable {m : ℕ} [NeZero m] {v : Fin m → ℝ × ℝ}

lemma sideTangent_nrm (i : Fin m) : sideTangent (nrm v i) = tng v i := by
  apply Prod.ext <;> simp [sideTangent, nrm]

lemma sideChart_start (hm : 3 ≤ m) (hv : ConvexPos v) (i : Fin m) :
    sideChart (nrm v i) (hsup v i) (aEnd v i, 0) = v i := by
  have he := sideChart_coords (nrm v i) (nrm_unit (nondeg_of_convex hm hv) i) (hsup v i) (v i)
  have hc : sideCoords (nrm v i) (hsup v i) (v i) = (aEnd v i, 0) := by
    simp [sideCoords, sideTangent_nrm, aEnd, hsup]
  rw [hc] at he; exact he

lemma sideChart_end (hm : 3 ≤ m) (hv : ConvexPos v) (i : Fin m) :
    sideChart (nrm v i) (hsup v i) (bEnd v i, 0) = v (i + 1) := by
  have he := sideChart_coords (nrm v i) (nrm_unit (nondeg_of_convex hm hv) i)
    (hsup v i) (v (i + 1))
  have hc : sideCoords (nrm v i) (hsup v i) (v (i + 1)) = (bEnd v i, 0) := by
    simp [sideCoords, sideTangent_nrm, bEnd, hsup_succ]
  rw [hc] at he; exact he

lemma vertex_support_le (hv : ConvexPos v) (i j : Fin m) :
    dot (v j) (nrm v i) ≤ hsup v i := by
  by_cases h : j = i
  · subst j; exact le_rfl
  by_cases h' : j = i + 1
  · rw [h', hsup_succ]
  exact (hv i j h h').le

lemma affine_strict_inside {A B a b c s : ℝ} (has : a < s) (hsb : s < b)
    (ha : A + B * a ≤ c) (hb : A + B * b ≤ c)
    (hstrict : A + B * a < c ∨ A + B * b < c) : A + B * s < c := by
  have hab : 0 < b - a := by linarith
  have he : (b - a) * (c - (A + B * s)) =
      (b - s) * (c - (A + B * a)) + (s - a) * (c - (A + B * b)) := by ring
  have hpos : 0 < (b - a) * (c - (A + B * s)) := by
    rw [he]
    rcases hstrict with h | h
    · exact add_pos_of_pos_of_nonneg (mul_pos (by linarith) (by linarith))
        (mul_nonneg (by linarith) (by linarith))
    · exact add_pos_of_nonneg_of_pos (mul_nonneg (by linarith) (by linarith))
        (mul_pos (by linarith) (by linarith))
  have := (mul_pos_iff_of_pos_left hab).mp hpos
  linarith

lemma dot_sideChart_affine (u w : ℝ × ℝ) (h s d : ℝ) :
    dot (sideChart u h (s, d)) w = (h - d) * dot u w + s * dot (sideTangent u) w := by
  simp only [sideChart, sideTangent, dot]; ring

/-- An interior point of a side is strictly inside every other supporting half-plane. -/
lemma sideChart_strict_other (hm : 3 ≤ m) (hv : ConvexPos v) (i j : Fin m) (hji : j ≠ i)
    {s : ℝ} (ha : aEnd v i < s) (hb : s < bEnd v i) :
    dot (sideChart (nrm v i) (hsup v i) (s, 0)) (nrm v j) < hsup v j := by
  have hstart := vertex_support_le hv j i
  have hend := vertex_support_le hv j (i + 1)
  obtain ⟨w, hw, hwj, hwj1⟩ := side_vertex_off hm hji
  have hstrict : dot (v i) (nrm v j) < hsup v j ∨
      dot (v (i + 1)) (nrm v j) < hsup v j := by
    have h := hv j w hwj hwj1
    rcases hw with hw | hw
    · rw [hw] at h; exact Or.inl h
    · rw [hw] at h; exact Or.inr h
  rw [← sideChart_start hm hv i, dot_sideChart_affine] at hstart hstrict
  rw [← sideChart_end hm hv i, dot_sideChart_affine] at hend hstrict
  rw [dot_sideChart_affine]
  have ht := affine_strict_inside (A := hsup v i * dot (nrm v i) (nrm v j))
    (B := dot (sideTangent (nrm v i)) (nrm v j)) ha hb
    (by simpa only [sub_zero, mul_comm] using hstart)
    (by simpa only [sub_zero, mul_comm] using hend)
    (by simpa only [sub_zero, mul_comm] using hstrict)
  simpa only [sub_zero, mul_comm] using ht

lemma affine_le_max_endpoints (u w : ℝ × ℝ) (h d a b s : ℝ) (hs : s ∈ Icc a b) :
    dot (sideChart u h (s, d)) w ≤
      max (dot (sideChart u h (a, d)) w) (dot (sideChart u h (b, d)) w) := by
  simp only [dot_sideChart_affine]
  rcases le_total 0 (dot (sideTangent u) w) with hB | hB
  · calc _ ≤ (h - d) * dot u w + b * dot (sideTangent u) w := by
           nlinarith [mul_le_mul_of_nonneg_right hs.2 hB]
         _ ≤ _ := le_max_right _ _
  · calc _ ≤ (h - d) * dot u w + a * dot (sideTangent u) w := by
           nlinarith [mul_le_mul_of_nonpos_right hs.1 hB]
         _ ≤ _ := le_max_left _ _

/-- The physical position/depth rectangle on one side. -/
def sideWindow (K : Sides m) (i : Fin m) (a b d : ℝ) : Set (ℝ × ℝ) :=
  sideChart (K.u i) (K.h i) '' (Icc a b ×ˢ Icc 0 d)

omit [NeZero m] in
lemma isCompact_sideWindow (K : Sides m) (i : Fin m) (a b d : ℝ) :
    IsCompact (sideWindow K i a b d) :=
  (isCompact_Icc.prod isCompact_Icc).image (continuous_sideChart _ _)

omit [NeZero m] in
lemma measurableSet_sideWindow (K : Sides m) (i : Fin m) (a b d : ℝ) :
    MeasurableSet (sideWindow K i a b d) := (isCompact_sideWindow K i a b d).measurableSet

/-- A trimmed side interval admits a positive depth whose entire rectangle is in the polygon. -/
theorem exists_sideWindow_subset (hm : 3 ≤ m) (hv : ConvexPos v) (harea : area v = 1)
    (i : Fin m) {a b : ℝ} (ha : aEnd v i < a) (hab : a ≤ b) (hb : b < bEnd v i) :
    let K := sidesOf v hm hv harea
    ∃ d₀ > 0, ∀ d ∈ Icc 0 d₀, sideWindow K i a b d ⊆ polygonRegion K := by
  intro K
  have hj (j : Fin m) (hji : j ≠ i) : ∀ᶠ d : ℝ in 𝓝 0,
      dot (sideChart (nrm v i) (hsup v i) (a, d)) (nrm v j) < hsup v j ∧
      dot (sideChart (nrm v i) (hsup v i) (b, d)) (nrm v j) < hsup v j := by
    have ha0 := sideChart_strict_other hm hv i j hji ha (hab.trans_lt hb)
    have hb0 := sideChart_strict_other hm hv i j hji (ha.trans_le hab) hb
    have hca : Continuous (fun d : ℝ => dot (sideChart (nrm v i) (hsup v i) (a, d)) (nrm v j)) := by
      unfold sideChart dot; fun_prop
    have hcb : Continuous (fun d : ℝ => dot (sideChart (nrm v i) (hsup v i) (b, d)) (nrm v j)) := by
      unfold sideChart dot; fun_prop
    exact ((hca.tendsto 0).eventually (Iio_mem_nhds ha0)).and
      ((hcb.tendsto 0).eventually (Iio_mem_nhds hb0))
  have hall : ∀ᶠ d : ℝ in 𝓝 0, ∀ j : Fin m, j ≠ i →
      dot (sideChart (K.u i) (K.h i) (a, d)) (K.u j) < K.h j ∧
      dot (sideChart (K.u i) (K.h i) (b, d)) (K.u j) < K.h j := by
    apply eventually_all.mpr
    intro j
    by_cases hji : j ≠ i
    · exact (hj j hji).mono fun d hd _ => hd
    · exact Eventually.of_forall fun d h => (hji h).elim
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp hall
  refine ⟨r / 2, by positivity, ?_⟩
  intro d hd x hx j
  obtain ⟨q, hq, rfl⟩ := hx
  have hsmall : dist q.2 0 < r := by
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hq.2.1]
    linarith [hq.2.2, hd.2]
  by_cases hji : j = i
  · subst j
    have he := congrArg Prod.snd (sideCoords_chart (K.u i)
      (nrm_unit (nondeg_of_convex hm hv) i) (K.h i) q)
    change K.h i - dot (sideChart (K.u i) (K.h i) q) (K.u i) = q.2 at he
    linarith [hq.2.1]
  · have hends := hball hsmall j hji
    exact (affine_le_max_endpoints (K.u i) (K.u j) (K.h i) q.2 a b q.1 hq.1).trans
      (max_le hends.1.le hends.2.le)

omit [NeZero m] in
/-- Rectangle area in the physical polygon's coordinates, with no asymptotic Jacobian. -/
theorem sideWindow_volume (K : Sides m) (hG : GoodSides K) (i : Fin m) (a b d : ℝ) :
    volume (sideWindow K i a b d) = ENNReal.ofReal (b - a) * ENNReal.ofReal d :=
  sideChart_rectangle_volume (K.u i) (hG.unit i) (K.h i) a b d

end Enclosing
