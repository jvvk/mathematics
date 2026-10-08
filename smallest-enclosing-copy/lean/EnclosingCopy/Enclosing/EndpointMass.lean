import EnclosingCopy.Enclosing.EndpointGeometry

/-!
# Probability mass omitted by endpoint trimming

The omitted physical strip is covered by two endpoint rectangles. Their widths
are the trim margin plus the linear corner excess, giving an exact quadratic
upper bound, normalized by the actual physical area.
-/
namespace Enclosing
open MeasureTheory Set
variable {m : ℕ} [NeZero m] {v : Fin m → ℝ × ℝ}

/-- The physical boundary points omitted on a single trimmed side. -/
def endpointRemainder (K : Sides m) (i : Fin m) (δ d : ℝ) : Set (ℝ × ℝ) :=
  physicalSideStrip K i d \ sideWindow K i (K.a i + δ) (K.b i - δ) d

omit [NeZero m] in
lemma measurableSet_endpointRemainder (K : Sides m) (i : Fin m) (δ d : ℝ) :
    MeasurableSet (endpointRemainder K i δ d) :=
  (measurableSet_physicalSideStrip K i d).diff (measurableSet_sideWindow K i _ _ d)

/-- A normalized physical subset has mass equal to its area divided by polygon area. -/
lemma polygonSample_real_subset (hm : 3 ≤ m) (hv : ConvexPos v) (harea : area v = 1)
    {S : Set (ℝ × ℝ)} (hS : S ⊆ polygonRegion (sidesOf v hm hv harea)) :
    (polygonSample v hm hv harea).real S =
      volume.real S / (volume (polygonRegion (sidesOf v hm hv harea))).toReal := by
  rw [measureReal_def, polygonSample, ProbabilityTheory.cond_apply
    (measurableSet_polygonRegion _), inter_eq_right.mpr hS,
    ENNReal.toReal_mul, ENNReal.toReal_inv]
  simp only [measureReal_def, div_eq_mul_inv, mul_comm]

omit [NeZero m] in
/-- Two explicit endpoint rectangles cover everything lost by trimming one side. -/
lemma endpointRemainder_subset (K : Sides m) (i : Fin m)
    {C δ d : ℝ} (henlarge : physicalSideStrip K i d ⊆
      sideWindow K i (K.a i - C * d) (K.b i + C * d) d) :
    endpointRemainder K i δ d ⊆
      sideWindow K i (K.a i - C * d) (K.a i + δ) d ∪
      sideWindow K i (K.b i - δ) (K.b i + C * d) d := by
  intro x hx
  obtain ⟨q, hq, hqx⟩ := henlarge hx.1
  have hnot : ¬ (K.a i + δ ≤ q.1 ∧ q.1 ≤ K.b i - δ) := by
    intro h
    exact hx.2 ⟨q, ⟨h, hq.2⟩, hqx⟩
  by_cases hleft : q.1 ≤ K.a i + δ
  · exact Or.inl ⟨q, ⟨⟨hq.1.1, hleft⟩, hq.2⟩, hqx⟩
  · have hright : K.b i - δ ≤ q.1 := by
      by_contra h
      exact hnot ⟨(lt_of_not_ge hleft).le, (lt_of_not_ge h).le⟩
    exact Or.inr ⟨q, ⟨⟨hright, hq.1.2⟩, hq.2⟩, hqx⟩

/-- Single-side omission costs at most `2 (δ + C d) d / A`. -/
theorem exists_endpointRemainder_mass_bound (hm : 3 ≤ m) (hv : ConvexPos v)
    (harea : area v = 1) (i : Fin m) :
    let K := sidesOf v hm hv harea
    ∃ C ≥ 0, ∀ δ ≥ 0, ∀ d ≥ 0,
      (polygonSample v hm hv harea).real (endpointRemainder K i δ d) ≤
        2 * (δ + C * d) * d / (volume (polygonRegion K)).toReal := by
  intro K
  obtain ⟨C, hC, henlarge⟩ := exists_physicalSideStrip_enlargement hm hv harea i
  refine ⟨C, hC, ?_⟩
  intro δ hδ d hd
  have hwidth : 0 ≤ δ + C * d := add_nonneg hδ (mul_nonneg hC hd)
  let W₁ := sideWindow K i (K.a i - C * d) (K.a i + δ) d
  let W₂ := sideWindow K i (K.b i - δ) (K.b i + C * d) d
  have hfinite : volume (W₁ ∪ W₂) ≠ ⊤ :=
    ((isCompact_sideWindow K i _ _ d).union (isCompact_sideWindow K i _ _ d)).measure_ne_top
  have hle := (measureReal_mono
    (endpointRemainder_subset K i (henlarge d hd)) hfinite).trans
      (measureReal_union_le W₁ W₂)
  have hvol₁ : volume.real W₁ = (δ + C * d) * d := by
    rw [measureReal_def, sideWindow_volume K (goodSides_of_convex hm hv harea)]
    rw [show K.a i + δ - (K.a i - C * d) = δ + C * d by ring,
      ENNReal.toReal_mul, ENNReal.toReal_ofReal hwidth, ENNReal.toReal_ofReal hd]
  have hvol₂ : volume.real W₂ = (δ + C * d) * d := by
    rw [measureReal_def, sideWindow_volume K (goodSides_of_convex hm hv harea)]
    rw [show K.b i + C * d - (K.b i - δ) = δ + C * d by ring,
      ENNReal.toReal_mul, ENNReal.toReal_ofReal hwidth, ENNReal.toReal_ofReal hd]
  rw [hvol₁, hvol₂] at hle
  rw [polygonSample_real_subset hm hv harea (fun _ hx => hx.1.1)]
  apply div_le_div_of_nonneg_right _ (physical_area_pos hm hv harea).le
  nlinarith

/-- The union of physical boundary points missed by the trimmed side family. -/
def omittedBoundary (K : Sides m) (δ d : ℝ) : Set (ℝ × ℝ) :=
  ⋃ i : Fin m, endpointRemainder K i δ d

omit [NeZero m] in
lemma measurableSet_omittedBoundary (K : Sides m) (δ d : ℝ) :
    MeasurableSet (omittedBoundary K δ d) :=
  MeasurableSet.iUnion fun i => measurableSet_endpointRemainder K i δ d

/-- The full omission bound, uniform in the endpoint margin and depth. -/
theorem exists_omittedBoundary_mass_bound (hm : 3 ≤ m) (hv : ConvexPos v)
    (harea : area v = 1) :
    let K := sidesOf v hm hv harea
    ∃ C ≥ 0, ∀ δ ≥ 0, ∀ d ≥ 0,
      (polygonSample v hm hv harea).real (omittedBoundary K δ d) ≤
        ((2 * (m : ℝ) * δ + C * d) * d) / (volume (polygonRegion K)).toReal := by
  classical
  intro K
  choose C hC hbound using exists_endpointRemainder_mass_bound hm hv harea
  refine ⟨2 * ∑ i, C i, mul_nonneg (by norm_num) (Finset.sum_nonneg fun i _ => hC i), ?_⟩
  intro δ hδ d hd
  calc
    _ ≤ ∑ i, (polygonSample v hm hv harea).real (endpointRemainder K i δ d) :=
      measureReal_iUnion_fintype_le _
    _ ≤ ∑ i, 2 * (δ + C i * d) * d / (volume (polygonRegion K)).toReal :=
      Finset.sum_le_sum fun i _ => hbound i δ hδ d hd
    _ = _ := by
      simp only [div_eq_mul_inv]
      simp_rw [mul_add, add_mul]
      simp only [Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum,
        Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring_nf

end Enclosing
