import EnclosingCopy.Enclosing.PhysicalStripMass
import EnclosingCopy.Enclosing.PhysicalBoundary

/-!
# First-order area of boundary strips with different side depths

Deleting a common corner exceptional set makes the side strips disjoint. Its
quadratic area is negligible, so the union has the sum of the single-side rates.
-/
namespace Enclosing
open MeasureTheory Set Filter Topology

lemma finite_union_mass_lower {α ι : Type*} [MeasurableSpace α] [Fintype ι]
    (μ : Measure α) [IsFiniteMeasure μ] (S : ι → Set α) (hS : ∀ i, MeasurableSet (S i))
    (C : Set α) (hC : MeasurableSet C)
    (hoverlap : ∀ i j, i ≠ j → S i ∩ S j ⊆ C) :
    (∑ i, μ.real (S i)) - (Fintype.card ι : ℝ) * μ.real C ≤ μ.real (⋃ i, S i) := by
  have hdis : Pairwise (fun i j => Disjoint (S i \ C) (S j \ C)) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro x hxi hxj
    exact hxi.2 (hoverlap i j hij ⟨hxi.1, hxj.1⟩)
  have hpoint (i : ι) : μ.real (S i) ≤ μ.real (S i \ C) + μ.real C := by
    have hsub : S i ⊆ (S i \ C) ∪ C := by
      intro x hx
      by_cases hc : x ∈ C
      · exact Or.inr hc
      · exact Or.inl ⟨hx, hc⟩
    exact (measureReal_mono (μ := μ) hsub).trans (measureReal_union_le _ _)
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hpoint i)
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    ← measureReal_iUnion_fintype hdis (fun i => (hS i).diff hC)] at hsum
  have hmono := measureReal_mono (μ := μ)
    (show (⋃ i, S i \ C) ⊆ ⋃ i, S i from iUnion_mono fun _ => sdiff_subset)
  linarith

variable {m : ℕ} [NeZero m] {v : Fin m → ℝ × ℝ}

def weightedBoundaryWindow (K : Sides m) (y : Fin m → ℝ) (n : ℕ) : Set (ℝ × ℝ) :=
  ⋃ i, physicalSideStrip K i (y i / n)

omit [NeZero m] in
lemma measurableSet_weightedBoundaryWindow (K : Sides m) (y : Fin m → ℝ) (n : ℕ) :
    MeasurableSet (weightedBoundaryWindow K y n) :=
  MeasurableSet.iUnion fun i => measurableSet_physicalSideStrip K i _

theorem weightedBoundaryWindow_scaled_mass (hm : 3 ≤ m) (hv : ConvexPos v)
    (harea : area v = 1) (y : Fin m → ℝ) (hy : ∀ i, 0 ≤ y i) :
    let K := sidesOf v hm hv harea
    Tendsto (fun n : ℕ => (n : ℝ) * (polygonSample v hm hv harea).real
      (weightedBoundaryWindow K y n)) atTop
      (𝓝 ((∑ i, (K.b i - K.a i) * y i) / (volume (polygonRegion K)).toReal)) := by
  intro K
  let μ := polygonSample v hm hv harea
  let A := (volume (polygonRegion K)).toReal
  let M := ∑ i, y i
  have hM : 0 ≤ M := Finset.sum_nonneg fun i _ => hy i
  have hMi (i : Fin m) : y i ≤ M :=
    Finset.single_le_sum (fun j _ => hy j) (Finset.mem_univ i)
  have hsum : Tendsto (fun n : ℕ => ∑ i, (n : ℝ) * μ.real
      (physicalSideStrip K i (y i / n))) atTop
      (𝓝 ((∑ i, (K.b i - K.a i) * y i) / A)) := by
    have h := tendsto_finsetSum Finset.univ
      (fun i _ => physicalSideStrip_scaled_mass hm hv harea i (hy i))
    simpa only [Finset.sum_div] using h
  have hcorner : Tendsto (fun n : ℕ => (m : ℝ) * ((n : ℝ) * μ.real
      (cornerOverlap K (M / n)))) atTop (𝓝 0) := by
    simpa using (cornerOverlap_scaled_mass_zero hm hv harea hM).const_mul (m : ℝ)
  have hlower (n : ℕ) :
      (∑ i, (n : ℝ) * μ.real (physicalSideStrip K i (y i / n))) -
        (m : ℝ) * ((n : ℝ) * μ.real (cornerOverlap K (M / n))) ≤
      (n : ℝ) * μ.real (weightedBoundaryWindow K y n) := by
    have hoverlap (i j : Fin m) (hij : i ≠ j) :
        physicalSideStrip K i (y i / n) ∩ physicalSideStrip K j (y j / n) ⊆
          cornerOverlap K (M / n) := by
      intro x hx
      apply mem_cornerOverlap_of_strips K hij
      · exact ⟨hx.1.1, hx.1.2.1, hx.1.2.2.trans
          (div_le_div_of_nonneg_right (hMi i) (Nat.cast_nonneg n))⟩
      · exact ⟨hx.2.1, hx.2.2.1, hx.2.2.2.trans
          (div_le_div_of_nonneg_right (hMi j) (Nat.cast_nonneg n))⟩
    have h := mul_le_mul_of_nonneg_left (finite_union_mass_lower μ
      (fun i => physicalSideStrip K i (y i / n))
      (fun i => measurableSet_physicalSideStrip K i _) (cornerOverlap K (M / n))
      (measurableSet_cornerOverlap K _) hoverlap) (Nat.cast_nonneg n)
    simpa only [Fintype.card_fin, mul_sub, Finset.mul_sum, mul_left_comm,
      weightedBoundaryWindow] using h
  have hupper (n : ℕ) : (n : ℝ) * μ.real (weightedBoundaryWindow K y n) ≤
      ∑ i, (n : ℝ) * μ.real (physicalSideStrip K i (y i / n)) := by
    simpa only [Finset.mul_sum, weightedBoundaryWindow] using mul_le_mul_of_nonneg_left
      (measureReal_iUnion_fintype_le (μ := μ) (fun i => physicalSideStrip K i (y i / n)))
      (Nat.cast_nonneg n)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le (by simpa using hsum.sub hcorner)
    hsum hlower hupper

theorem weightedBoundaryWindow_scaled_volume (hm : 3 ≤ m) (hv : ConvexPos v)
    (harea : area v = 1) (y : Fin m → ℝ) (hy : ∀ i, 0 ≤ y i) :
    let K := sidesOf v hm hv harea
    Tendsto (fun n : ℕ => (n : ℝ) * volume.real (weightedBoundaryWindow K y n))
      atTop (𝓝 (∑ i, (K.b i - K.a i) * y i)) := by
  intro K
  let A := (volume (polygonRegion K)).toReal
  have hA : A ≠ 0 := (physical_area_pos hm hv harea).ne'
  have h := (weightedBoundaryWindow_scaled_mass hm hv harea y hy).const_mul A
  have hsub (n : ℕ) : weightedBoundaryWindow K y n ⊆ polygonRegion K := by
    intro x hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    exact hi.1
  convert h using 1
  · funext n
    rw [polygonSample_real_subset hm hv harea
      (S := weightedBoundaryWindow (sidesOf v hm hv harea) y n) (hsub n)]
    change (n : ℝ) * volume.real (weightedBoundaryWindow K y n) =
      A * ((n : ℝ) * (volume.real (weightedBoundaryWindow K y n) / A))
    field_simp
  · congr 1
    change (∑ i, (K.b i - K.a i) * y i) = A * ((∑ i, (K.b i - K.a i) * y i) / A)
    field_simp

end Enclosing
