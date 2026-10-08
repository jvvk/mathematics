import EnclosingCopy.Enclosing.HomothetyGeometry
import EnclosingCopy.Enclosing.WeightedBoundaryMass
import EnclosingCopy.Enclosing.FullBoundaryLimit

/-!
# Physical Lebesgue area agrees with the area-one normalization

A small homothetic contraction removes a shell of area `A (2t-t²)`. Its boundary
strips have first-order area `t ∑ Lᵢ gᵢ = 2t`, by the support-gap identity. Comparing
these two limits proves `A = 1` without presupposing a polygon-area formula.
-/
namespace Enclosing
open MeasureTheory Set Filter Topology
open scoped ENNReal
variable {m : ℕ} [NeZero m]

lemma boundary_shell_real_volume (K : Sides m) (hG : GoodSides K)
    {w : ℝ × ℝ} (hw : w ∈ polygonRegion K) {n : ℕ} (hn : 1 < n) :
    volume.real (weightedBoundaryWindow K (fun i => K.h i - dot w (K.u i)) n) =
      volume.real (polygonRegion K) -
        (1 - 1 / (n : ℝ)) ^ 2 * volume.real (polygonRegion K) := by
  classical
  have hn' : (1 : ℝ) < n := by exact_mod_cast hn
  have ht : (1 : ℝ) / n < 1 := (div_lt_one (by linarith)).mpr hn'
  have h0 : 0 ≤ (1 : ℝ) / n := by positivity
  let L : Set (ℝ × ℝ) := ⋃ i : Fin m,
    {x | K.h i - dot x (K.u i) = (K.h i - dot w (K.u i)) / n}
  have hL : volume L = 0 := measure_iUnion_null fun i => depth_level_volume_zero K hG i _
  have he : weightedBoundaryWindow K (fun i => K.h i - dot w (K.u i)) n =ᵐ[volume]
      polygonRegion K \ contractedRegion K w (1 / n) := by
    have ha : ∀ᵐ x : ℝ × ℝ ∂volume, x ∉ L := by
      rw [ae_iff]
      simpa only [not_not, ofPred_mem_eq] using hL
    filter_upwards [ha] with x hx
    apply propext
    constructor
    · intro h
      obtain ⟨i, hi⟩ := mem_iUnion.mp h
      refine ⟨hi.1, ?_⟩
      intro hc
      have hg := (mem_contractedRegion_iff K w ht x).mp hc i
      have hg' : (K.h i - dot w (K.u i)) / (n : ℝ) ≤ K.h i - dot x (K.u i) := by
        simpa only [one_div, div_eq_mul_inv, mul_comm, mul_one, one_mul] using hg
      exact hx (mem_iUnion.mpr ⟨i, le_antisymm hi.2.2 hg'⟩)
    · intro h
      have hnall : ¬ ∀ i, (1 / (n : ℝ)) * (K.h i - dot w (K.u i)) ≤
          K.h i - dot x (K.u i) := fun hall => h.2 ((mem_contractedRegion_iff K w ht x).mpr hall)
      obtain ⟨i, hi⟩ := not_forall.mp hnall
      apply mem_iUnion.mpr
      refine ⟨i, h.1, sub_nonneg.mpr (h.1 i), ?_⟩
      have hg := (lt_of_not_ge hi).le
      simpa only [one_div, div_eq_mul_inv, mul_comm, mul_one, one_mul] using hg
  rw [measureReal_def, measure_congr he, ← measureReal_def,
    measureReal_sdiff (contractedRegion_subset K hw h0 ht.le)
      (isCompact_contractedRegion K hG w _).measurableSet
      (polygonRegion_volume_ne_top K hG), contractedRegion_real_volume]

variable {v : Fin m → ℝ × ℝ}

/-- **The physical half-plane polygon has area one.** The area normalization in
`sidesOf` is now identified with actual planar Lebesgue measure. -/
theorem polygonRegion_real_volume_one (hm : 3 ≤ m) (hv : ConvexPos v)
    (harea : area v = 1) :
    volume.real (polygonRegion (sidesOf v hm hv harea)) = 1 := by
  let K := sidesOf v hm hv harea
  let w := v 0
  have hw : w ∈ polygonRegion K := fun i => vertex_support_le hv i 0
  let y := fun i => K.h i - dot w (K.u i)
  have hy (i : Fin m) : 0 ≤ y i := sub_nonneg.mpr (hw i)
  let A := volume.real (polygonRegion K)
  have hs : Tendsto (fun n : ℕ => (n : ℝ) * volume.real (weightedBoundaryWindow K y n))
      atTop (𝓝 2) := by
    have h := weightedBoundaryWindow_scaled_volume hm hv harea y hy
    change Tendsto (fun n : ℕ => (n : ℝ) * volume.real (weightedBoundaryWindow K y n))
      atTop (𝓝 (∑ i, (K.b i - K.a i) * (K.h i - dot w (K.u i)))) at h
    rwa [support_gap_sum] at h
  have he : (fun n : ℕ => (n : ℝ) * volume.real (weightedBoundaryWindow K y n)) =ᶠ[atTop]
      (fun n => 2 * A - A / n) := by
    filter_upwards [eventually_gt_atTop 1] with n hn
    rw [boundary_shell_real_volume K (goodSides_of_convex hm hv harea) hw hn]
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
    change (n : ℝ) * (A - (1 - 1 / n) ^ 2 * A) = 2 * A - A / n
    field_simp
    ring
  have hs' : Tendsto (fun n : ℕ => 2 * A - A / n) atTop (𝓝 2) := hs.congr' he
  have ht : Tendsto (fun n : ℕ => 2 * A - A / n) atTop (𝓝 (2 * A)) := by
    simpa using tendsto_const_nhds.sub (tendsto_const_div_atTop_nhds_zero_nat A)
  have hA := tendsto_nhds_unique ht hs'
  change A = 1
  linarith

theorem polygonRegion_volume_one (hm : 3 ≤ m) (hv : ConvexPos v) (harea : area v = 1) :
    volume (polygonRegion (sidesOf v hm hv harea)) = 1 := by
  apply (ENNReal.toReal_eq_toReal_iff'
    (polygonRegion_volume_ne_top _ (goodSides_of_convex hm hv harea)) (by simp)).mp
  simpa only [ENNReal.toReal_one, ← measureReal_def] using
    polygonRegion_real_volume_one hm hv harea

/-- Uniform sampling now equals the unnormalized volume restriction, since area is one. -/
theorem polygonSample_eq_volume_restrict (hm : 3 ≤ m) (hv : ConvexPos v)
    (harea : area v = 1) :
    polygonSample v hm hv harea = volume.restrict (polygonRegion (sidesOf v hm hv harea)) := by
  rw [polygonSample, ProbabilityTheory.cond, polygonRegion_volume_one hm hv harea]
  simp

/-- The full boundary process has the paper's intensity, with no area denominator. -/
theorem polygon_boundary_event_limit (hm : 3 ≤ m) (hv : ConvexPos v)
    (harea : area v = 1) {T : ℝ} (hT : 0 < T) (F : Multiset (Pt m) → Prop)
    (hF : ∀ k, MeasurableSet {x : Fin k → Pt m | F (PoissonPP.config x)}) :
    let K := sidesOf v hm hv harea
    Tendsto (fun n : ℕ => (Measure.pi fun _ : Fin n => polygonSample v hm hv harea).real
      {x | F ((PoissonPP.inWindow (physicalBoundaryWindow K T n) (PoissonPP.config x)).map
        (physicalBoundaryMark K T n))}) atTop
      (𝓝 ((PoissonPP.law (Λ K T)).real {ω | F (PoissonPP.config ω.2)})) := by
  intro K
  have h := polygon_full_boundary_event_limit hm hv harea hT F hF
  simpa only [polygonRegion_volume_one hm hv harea, ENNReal.toReal_one, inv_one,
    ENNReal.ofReal_one, one_smul] using h

end Enclosing
