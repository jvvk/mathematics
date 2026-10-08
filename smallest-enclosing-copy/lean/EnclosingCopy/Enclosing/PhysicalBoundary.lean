import EnclosingCopy.Enclosing.BoundaryLimit
import EnclosingCopy.Enclosing.EndpointSampling
import EnclosingCopy.Enclosing.PolygonOverlap

/-!
# Full physical boundary configurations and trimmed approximations

The physical window consists of all polygon points within depth `T/n` of any
supporting line. Away from endpoint omissions and corner overlaps its marked
configuration agrees exactly with the trimmed configuration.
-/
namespace Enclosing
open MeasureTheory Set Filter Topology
variable {m : ℕ} [NeZero m] {v : Fin m → ℝ × ℝ}

def physicalBoundaryWindow (K : Sides m) (T : ℝ) (n : ℕ) : Set (ℝ × ℝ) :=
  ⋃ i, physicalSideStrip K i (T / n)

noncomputable def physicalBoundaryMark (K : Sides m) (T : ℝ) (n : ℕ) : (ℝ × ℝ) → Pt m :=
  PoissonPP.glueWindows (List.finRange m) (fun i => physicalSideStrip K i (T / n))
    (fun i x => (i, sideMark K i n x)) (fun _ => (0, 0, 0))

omit [NeZero m] in
lemma measurableSet_physicalBoundaryWindow (K : Sides m) (T : ℝ) (n : ℕ) :
    MeasurableSet (physicalBoundaryWindow K T n) :=
  MeasurableSet.iUnion fun i => measurableSet_physicalSideStrip K i _

lemma measurable_physicalBoundaryMark (K : Sides m) (T : ℝ) (n : ℕ) :
    Measurable (physicalBoundaryMark K T n) :=
  PoissonPP.measurable_glueWindows _ _ _ _
    (fun i => measurableSet_physicalSideStrip K i _)
    (fun i => measurable_const.prodMk (measurable_sideMark K i n)) measurable_const

lemma measurableSet_physicalBoundary_event (K : Sides m) (T : ℝ) (n k : ℕ)
    (F : Multiset (Pt m) → Prop)
    (hF : ∀ j, MeasurableSet {x : Fin j → Pt m | F (PoissonPP.config x)}) :
    MeasurableSet {x : Fin k → ℝ × ℝ |
      F ((PoissonPP.inWindow (physicalBoundaryWindow K T n) (PoissonPP.config x)).map
        (physicalBoundaryMark K T n))} :=
  PoissonPP.measurableSet_window_event (measurableSet_physicalBoundaryWindow K T n)
    (physicalBoundaryMark K T n) (measurable_physicalBoundaryMark K T n) F hF

omit [NeZero m] in
lemma sideWindow_subset_physicalSideStrip (K : Sides m) (hG : GoodSides K)
    (i : Fin m) {a b d : ℝ} (hsub : sideWindow K i a b d ⊆ polygonRegion K) :
    sideWindow K i a b d ⊆ physicalSideStrip K i d := by
  intro x hx
  refine ⟨hsub hx, ?_⟩
  obtain ⟨q, hq, rfl⟩ := hx
  have he := congrArg Prod.snd (sideCoords_chart (K.u i) (hG.unit i) (K.h i) q)
  change K.h i - dot (sideChart (K.u i) (K.h i) q) (K.u i) = q.2 at he
  change K.h i - dot (sideChart (K.u i) (K.h i) q) (K.u i) ∈ Icc 0 d
  rw [he]
  exact hq.2

omit [NeZero m] in
lemma mem_cornerOverlap_of_strips (K : Sides m) {i j : Fin m} (hij : i ≠ j)
    {d : ℝ} {x : ℝ × ℝ} (hi : x ∈ physicalSideStrip K i d)
    (hj : x ∈ physicalSideStrip K j d) : x ∈ cornerOverlap K d := by
  apply mem_iUnion.mpr
  refine ⟨i, mem_iUnion.mpr ⟨j, ?_⟩⟩
  simp only [ite_eq_right hij]
  exact ⟨hi.1, hi.2, hj.2⟩

lemma physical_trimmed_mark_agreement (K : Sides m) (hG : GoodSides K)
    {δ T : ℝ} {n : ℕ}
    (hsub : ∀ i, sideWindow K i (K.a i + δ) (K.b i - δ) (T / n) ⊆ polygonRegion K)
    {x : ℝ × ℝ} (hmiss : x ∉ omittedBoundary K δ (T / n))
    (hcorner : x ∉ cornerOverlap K (T / n)) :
    (x ∈ physicalBoundaryWindow K T n ↔
      x ∈ boundaryWindow K (fun i => K.a i + δ) (fun i => K.b i - δ) T n) ∧
    (x ∈ physicalBoundaryWindow K T n → physicalBoundaryMark K T n x =
      boundaryMark K (fun i => K.a i + δ) (fun i => K.b i - δ) T n x) := by
  have htrim (i : Fin m) (hi : x ∈ physicalSideStrip K i (T / n)) :
      x ∈ sideWindow K i (K.a i + δ) (K.b i - δ) (T / n) := by
    by_contra h
    exact hmiss (mem_iUnion.mpr ⟨i, hi, h⟩)
  have hstrip (i : Fin m) := sideWindow_subset_physicalSideStrip K hG i (hsub i)
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    exact mem_iUnion.mpr ⟨i, htrim i hi⟩
  · intro hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    exact mem_iUnion.mpr ⟨i, hstrip i hi⟩
  · intro hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    have hunique (j : Fin m) (hji : j ≠ i) : x ∉ physicalSideStrip K j (T / n) := by
      intro hj
      exact hcorner (mem_cornerOverlap_of_strips K (Ne.symm hji) hi hj)
    have hp := PoissonPP.glueWindows_eq (List.finRange m)
      (fun i => physicalSideStrip K i (T / n)) (fun i x => (i, sideMark K i n x))
      (fun _ => (0, 0, 0)) i (List.mem_finRange i) hi (fun j _ => hunique j)
    have ht := PoissonPP.glueWindows_eq (List.finRange m)
      (fun i => sideWindow K i (K.a i + δ) (K.b i - δ) (T / n))
      (fun i x => (i, sideMark K i n x)) (fun _ => (0, 0, 0))
      i (List.mem_finRange i) (htrim i hi) (fun j _ hji hj => hunique j hji (hstrip j hj))
    exact hp.trans ht.symm

lemma physical_trimmed_config_agreement (K : Sides m) (hG : GoodSides K)
    {δ T : ℝ} {n : ℕ}
    (hsub : ∀ i, sideWindow K i (K.a i + δ) (K.b i - δ) (T / n) ⊆ polygonRegion K)
    {x : Fin n → ℝ × ℝ} (hmiss : x ∉ endpointHit K δ T n)
    (hcorner : ¬ ∃ j, x j ∈ cornerOverlap K (T / n)) :
    (PoissonPP.inWindow (physicalBoundaryWindow K T n) (PoissonPP.config x)).map
      (physicalBoundaryMark K T n) =
    (PoissonPP.inWindow (boundaryWindow K (fun i => K.a i + δ) (fun i => K.b i - δ) T n)
      (PoissonPP.config x)).map
      (boundaryMark K (fun i => K.a i + δ) (fun i => K.b i - δ) T n) := by
  classical
  have hpoint (p : ℝ × ℝ) (hp : p ∈ PoissonPP.config x) :
      (p ∈ physicalBoundaryWindow K T n ↔ p ∈
        boundaryWindow K (fun i => K.a i + δ) (fun i => K.b i - δ) T n) ∧
      (p ∈ physicalBoundaryWindow K T n → physicalBoundaryMark K T n p =
        boundaryMark K (fun i => K.a i + δ) (fun i => K.b i - δ) T n p) := by
    obtain ⟨j, rfl⟩ := (PoissonPP.mem_config x p).mp hp
    exact physical_trimmed_mark_agreement K hG hsub
      (fun h => hmiss ⟨j, h⟩) (fun h => hcorner ⟨j, h⟩)
  have he : PoissonPP.inWindow (physicalBoundaryWindow K T n) (PoissonPP.config x) =
      PoissonPP.inWindow (boundaryWindow K (fun i => K.a i + δ) (fun i => K.b i - δ) T n)
        (PoissonPP.config x) :=
    Multiset.filter_congr fun p hp => (hpoint p hp).1
  apply Multiset.map_congr he
  intro p hp
  have hp' := Multiset.mem_filter.mp hp
  exact (hpoint p hp'.1).2 ((hpoint p hp'.1).1.mpr hp'.2)

/-- Every configuration event changes only if a sampled point is omitted or ambiguous. -/
theorem physical_trimmed_event_diff_le (hm : 3 ≤ m) (hv : ConvexPos v)
    (harea : area v = 1) {δ T : ℝ} (hδ : 0 < δ)
    (hwidth : ∀ i, aEnd v i + δ ≤ bEnd v i - δ) (hT : 0 ≤ T)
    (F : Multiset (Pt m) → Prop) :
    let K := sidesOf v hm hv harea
    ∀ᶠ n : ℕ in atTop,
      |(Measure.pi fun _ : Fin n => polygonSample v hm hv harea).real
        {x | F ((PoissonPP.inWindow (physicalBoundaryWindow K T n) (PoissonPP.config x)).map
          (physicalBoundaryMark K T n))} -
        (Measure.pi fun _ : Fin n => polygonSample v hm hv harea).real
        {x | F ((PoissonPP.inWindow
          (boundaryWindow K (fun i => K.a i + δ) (fun i => K.b i - δ) T n)
          (PoissonPP.config x)).map
          (boundaryMark K (fun i => K.a i + δ) (fun i => K.b i - δ) T n))}| ≤
        (Measure.pi fun _ : Fin n => polygonSample v hm hv harea).real (endpointHit K δ T n) +
        (Measure.pi fun _ : Fin n => polygonSample v hm hv harea).real
          {x | ∃ j, x j ∈ cornerOverlap K (T / n)} := by
  intro K
  filter_upwards [sideWindows_subset_eventually hm hv harea (fun i => K.a i + δ)
    (fun i => K.b i - δ) (fun i => lt_add_of_pos_right _ hδ) hwidth
    (fun i => sub_lt_self _ hδ) hT] with n hsub
  apply (PoissonPP.event_probability_diff_le _ (B := endpointHit K δ T n ∪
    {x | ∃ j, x j ∈ cornerOverlap K (T / n)}) ?_).trans
    (measureReal_union_le _ _)
  intro x hx
  have he := physical_trimmed_config_agreement K (goodSides_of_convex hm hv harea)
    hsub (fun h => hx (Or.inl h)) (fun h => hx (Or.inr h))
  simp only [mem_ofPred_eq, he]

end Enclosing
