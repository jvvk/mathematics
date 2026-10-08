import EnclosingCopy.Enclosing.SideChart

/-!
# The physical polygon region is compact

The polygon is the intersection of its closed supporting half-planes. The positive
side-length identity bounds the support gap at each side; any two nonparallel normals
then bound both physical coordinates. This proves finite area without assuming it.
-/
namespace Enclosing
open MeasureTheory Set Finset
variable {m : ℕ} (K : Sides m)

/-- The physical polygon defined by the supporting sides. -/
def polygonRegion : Set (ℝ × ℝ) := {x | ∀ i, dot x (K.u i) ≤ K.h i}

lemma isClosed_polygonRegion : IsClosed (polygonRegion K) := by
  have he : polygonRegion K = ⋂ i : Fin m, {x | dot x (K.u i) ≤ K.h i} := by
    ext; simp [polygonRegion]
  rw [he]
  apply isClosed_iInter
  intro i
  apply isClosed_le _ continuous_const
  unfold dot; fun_prop

lemma measurableSet_polygonRegion : MeasurableSet (polygonRegion K) :=
  (isClosed_polygonRegion K).measurableSet

lemma support_gap_sum (x : ℝ × ℝ) :
    ∑ i, (K.b i - K.a i) * (K.h i - dot x (K.u i)) = 2 := by
  have he : ∀ i, (K.b i - K.a i) * (K.h i - dot x (K.u i)) =
      (K.b i - K.a i) * K.h i - x.1 * ((K.b i - K.a i) * (K.u i).1) -
        x.2 * ((K.b i - K.a i) * (K.u i).2) := by intro i; unfold dot; ring
  simp_rw [he, Finset.sum_sub_distrib, ← Finset.mul_sum, K.sum_h, K.sum_u1, K.sum_u2]
  ring

/-- Support gaps have a bound depending only on the polygon. -/
lemma support_gap_le {x : ℝ × ℝ} (hx : x ∈ polygonRegion K) (i : Fin m) :
    K.h i - dot x (K.u i) ≤ 2 / (K.b i - K.a i) := by
  rw [le_div_iff₀ (sub_pos.mpr (K.hab i))]
  have hs := Finset.single_le_sum
    (s := Finset.univ) (f := fun j => (K.b j - K.a j) * (K.h j - dot x (K.u j)))
    (fun j _ => mul_nonneg (sub_pos.mpr (K.hab j)).le (sub_nonneg.mpr (hx j)))
    (Finset.mem_univ i)
  rw [support_gap_sum] at hs
  simpa only [mul_comm] using hs

lemma support_abs_le {x : ℝ × ℝ} (hx : x ∈ polygonRegion K) (i : Fin m) :
    |dot x (K.u i)| ≤ |K.h i| + 2 / (K.b i - K.a i) := by
  have hgap := support_gap_le K hx i
  have hd : 0 ≤ 2 / (K.b i - K.a i) := div_nonneg (by norm_num) (sub_pos.mpr (K.hab i)).le
  rw [abs_le]
  constructor
  · linarith [neg_abs_le (K.h i)]
  · linarith [le_abs_self (K.h i), hx i]

/-- Two nonparallel support bounds control both coordinates. -/
lemma coords_bounded (u v x : ℝ × ℝ) (huv : u.1 * v.2 - u.2 * v.1 ≠ 0)
    (cu cv : ℝ) (hu : |dot x u| ≤ cu) (hv : |dot x v| ≤ cv) :
    |x.1| ≤ (cu * (|v.1| + |v.2|) + cv * (|u.1| + |u.2|)) /
      |u.1 * v.2 - u.2 * v.1| ∧
    |x.2| ≤ (cu * (|v.1| + |v.2|) + cv * (|u.1| + |u.2|)) /
      |u.1 * v.2 - u.2 * v.1| := by
  have hc : 0 ≤ cu := (abs_nonneg _).trans hu
  have hd : 0 ≤ cv := (abs_nonneg _).trans hv
  have hx1 : x.1 = (dot x u * v.2 - dot x v * u.2) / (u.1 * v.2 - u.2 * v.1) := by
    apply (eq_div_iff huv).2; unfold dot; ring
  have hx2 : x.2 = (dot x v * u.1 - dot x u * v.1) / (u.1 * v.2 - u.2 * v.1) := by
    apply (eq_div_iff huv).2; unfold dot; ring
  constructor
  · rw [hx1, abs_div]
    apply div_le_div_of_nonneg_right _ (abs_nonneg _)
    calc _ ≤ |dot x u * v.2| + |dot x v * u.2| := abs_sub _ _
      _ ≤ cu * |v.2| + cv * |u.2| := by simp only [abs_mul]; gcongr
      _ ≤ _ := by nlinarith [mul_nonneg hc (abs_nonneg v.1), mul_nonneg hd (abs_nonneg u.1)]
  · rw [hx2, abs_div]
    apply div_le_div_of_nonneg_right _ (abs_nonneg _)
    calc _ ≤ |dot x v * u.1| + |dot x u * v.1| := abs_sub _ _
      _ ≤ cv * |u.1| + cu * |v.1| := by simp only [abs_mul]; gcongr
      _ ≤ _ := by nlinarith [mul_nonneg hc (abs_nonneg v.2), mul_nonneg hd (abs_nonneg u.2)]

variable [NeZero m]

/-- The half-plane polygon is compact; in particular, uniform sampling has finite area. -/
theorem isCompact_polygonRegion (hG : GoodSides K) : IsCompact (polygonRegion K) := by
  obtain ⟨j, hj⟩ := hG.nondeg (0 : Fin m)
  let cu := |K.h 0| + 2 / (K.b 0 - K.a 0)
  let cv := |K.h j| + 2 / (K.b j - K.a j)
  let B := (cu * (|(K.u j).1| + |(K.u j).2|) +
    cv * (|(K.u 0).1| + |(K.u 0).2|)) /
      |(K.u 0).1 * (K.u j).2 - (K.u 0).2 * (K.u j).1|
  refine (isCompact_Icc.prod isCompact_Icc).of_isClosed_subset (isClosed_polygonRegion K)
    (show polygonRegion K ⊆ Icc (-B) B ×ˢ Icc (-B) B from ?_)
  intro x hx
  have hb := coords_bounded (K.u 0) (K.u j) x hj cu cv
    (support_abs_le K hx 0) (support_abs_le K hx j)
  exact ⟨abs_le.mp hb.1, abs_le.mp hb.2⟩

lemma polygonRegion_volume_ne_top (hG : GoodSides K) : volume (polygonRegion K) ≠ ⊤ :=
  (isCompact_polygonRegion K hG).measure_lt_top.ne

end Enclosing
