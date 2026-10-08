import EnclosingCopy.Enclosing.PolygonArea
import EnclosingCopy.Poisson.FixedMarkComparison

/-!
# Uniform measurable-event convergence for the actual physical boundary process

The count comparison is independent of the event. Endpoint and corner errors
are also uniform, so arbitrary varying configuration events are covered at a
fixed depth cutoff. Optimum-event stabilization is `poisson_stable` (Theorem1Events).
-/
namespace Enclosing
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
variable {m : ℕ} [NeZero m] {v : Fin m → ℝ × ℝ}

theorem physical_trimmed_event_uniform_bound (hm : 3 ≤ m) (hv : ConvexPos v)
    (harea : area v = 1) {δ T : ℝ} (hδ : 0 < δ)
    (hwidth : ∀ i, aEnd v i + δ ≤ bEnd v i - δ) (hT : 0 ≤ T)
    :
    let K := sidesOf v hm hv harea
    ∀ᶠ n : ℕ in atTop, ∀ F : Multiset (Pt m) → Prop,
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
    (fun i => sub_lt_self _ hδ) hT] with n hsub F
  apply (PoissonPP.event_probability_diff_le _ (B := endpointHit K δ T n ∪
    {x | ∃ j, x j ∈ cornerOverlap K (T / n)}) ?_).trans
    (measureReal_union_le _ _)
  intro x hx
  have he := physical_trimmed_config_agreement K (goodSides_of_convex hm hv harea)
    hsub (fun h => hx (Or.inl h)) (fun h => hx (Or.inr h))
  simp only [mem_ofPred_eq, he]


/-- The trimmed boundary comparison is uniform over all measurable events. -/
theorem polygon_trimmed_uniform_event_error (hm : 3 ≤ m) (hv : ConvexPos v)
    (harea : area v = 1) (a b : Fin m → ℝ) (ha : ∀ i, aEnd v i < a i)
    (hab : ∀ i, a i < b i) (hb : ∀ i, b i < bEnd v i) {T : ℝ} (hT : 0 < T) :
    let K := sidesOf v hm hv harea
    let A := (volume (polygonRegion K)).toReal
    ∀ ε > 0, ∀ᶠ n : ℕ in atTop, ∀ F : Multiset (Pt m) → Prop,
      (∀ k, MeasurableSet {x : Fin k → Pt m | F (PoissonPP.config x)}) →
      |(Measure.pi fun _ : Fin n => polygonSample v hm hv harea).real
        {x | F ((PoissonPP.inWindow (boundaryWindow K a b T n) (PoissonPP.config x)).map
          (boundaryMark K a b T n))} -
        (PoissonPP.law (ENNReal.ofReal A⁻¹ • trimmedIntensity a b T)).real
          {ω | F (PoissonPP.config ω.2)}| < ε := by
  intro K A
  let _ := boundaryMarkLaw_probability a b hab hT
  let r : ℝ≥0 := ⟨(trimmedIntensity a b T).real univ / A,
    div_nonneg measureReal_nonneg (physical_area_pos hm hv harea).le⟩
  have he : (fun n : ℕ => (n : ℝ) * (polygonSample v hm hv harea).real
      (boundaryWindow K a b T n)) =ᶠ[atTop] (fun _ => (r : ℝ)) :=
    boundaryWindow_scaled_mass hm hv harea a b ha (fun i => (hab i).le) hb hT.le
  have hr : Tendsto (fun n : ℕ => (n : ℝ) * (polygonSample v hm hv harea).real
      (boundaryWindow K a b T n)) atTop (𝓝 (r : ℝ)) := tendsto_const_nhds.congr' he.symm
  have ht := PoissonPP.iid_fixed_mark_uniform_error (fun _ => polygonSample v hm hv harea)
    (boundaryWindow K a b T) (measurableSet_boundaryWindow K a b T)
    (boundaryMark K a b T) (measurable_boundaryMark K a b T) (boundaryMarkLaw a b T) hr
    (boundaryMarkLaw_eventually hm hv harea a b ha hab hb hT)
  have hnorm : (r : ℝ≥0∞) • boundaryMarkLaw a b T =
      ENNReal.ofReal A⁻¹ • trimmedIntensity a b T := by
    rw [← ENNReal.ofReal_coe_nnreal]
    exact boundary_intensity_normalization hm hv harea a b hab hT
  rwa [hnorm] at ht

/-- **Uniform full-window marked Poisson comparison.** At each fixed positive
cutoff, the actual boundary law converges uniformly on measurable configuration
events; in particular the events may depend on the sample size. -/
theorem polygon_full_boundary_uniform_error (hm : 3 ≤ m) (hv : ConvexPos v)
    (harea : area v = 1) {T : ℝ} (hT : 0 < T) :
    let K := sidesOf v hm hv harea
    let A := (volume (polygonRegion K)).toReal
    ∀ ε > 0, ∀ᶠ n : ℕ in atTop, ∀ F : Multiset (Pt m) → Prop,
      (∀ k, MeasurableSet {x : Fin k → Pt m | F (PoissonPP.config x)}) →
      |(Measure.pi fun _ : Fin n => polygonSample v hm hv harea).real
        {x | F ((PoissonPP.inWindow (physicalBoundaryWindow K T n)
          (PoissonPP.config x)).map (physicalBoundaryMark K T n))} -
        (PoissonPP.law (ENNReal.ofReal A⁻¹ • Λ K T)).real
          {ω | F (PoissonPP.config ω.2)}| < ε := by
  intro K A ε hε
  let p := fun (F : Multiset (Pt m) → Prop) (n : ℕ) =>
    (Measure.pi fun _ : Fin n => polygonSample v hm hv harea).real
      {x | F ((PoissonPP.inWindow (physicalBoundaryWindow K T n) (PoissonPP.config x)).map
        (physicalBoundaryMark K T n))}
  let q := fun F : Multiset (Pt m) → Prop =>
    (PoissonPP.law (ENNReal.ofReal A⁻¹ • Λ K T)).real {ω | F (PoissonPP.config ω.2)}
  change ∀ᶠ n in atTop, ∀ F, _ → |p F n - q F| < ε
  obtain ⟨C, _, hbound⟩ := exists_endpointHit_bound hm hv harea
  have hmargin : ∀ᶠ δ : ℝ in 𝓝 0,
      (∀ i : Fin m, K.a i + δ < K.b i - δ) ∧ 2 * (m : ℝ) * δ * T / A < ε / 8 := by
    have htrim : ∀ᶠ δ : ℝ in 𝓝 0, ∀ i : Fin m, K.a i + δ < K.b i - δ := by
      apply eventually_all.mpr
      intro i
      have hc : Continuous (fun δ : ℝ => K.a i + δ - (K.b i - δ)) := by fun_prop
      have hz : K.a i + 0 - (K.b i - 0) < 0 := by simpa using sub_neg.mpr (K.hab i)
      exact ((hc.tendsto 0).eventually (Iio_mem_nhds hz)).mono fun δ hδ => by linarith
    have hc : Continuous (fun δ : ℝ => 2 * (m : ℝ) * δ * T / A) := by fun_prop
    exact htrim.and ((hc.tendsto 0).eventually (Iio_mem_nhds (by simpa using
      (show (0 : ℝ) < ε / 8 by positivity))))
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp hmargin
  let δ := r / 2
  have hδ : 0 < δ := half_pos hr
  have hδr : dist δ 0 < r := by rw [Real.dist_eq, sub_zero, abs_of_pos hδ]; dsimp [δ]; linarith
  have hgood := hball hδr
  let a := fun i => K.a i + δ
  let b := fun i => K.b i - δ
  have ha (i : Fin m) : aEnd v i < a i := lt_add_of_pos_right _ hδ
  have hb (i : Fin m) : b i < bEnd v i := sub_lt_self _ hδ
  have hab (i : Fin m) : a i < b i := hgood.1 i
  let pt := fun (F : Multiset (Pt m) → Prop) (n : ℕ) =>
    (Measure.pi fun _ : Fin n => polygonSample v hm hv harea).real
    {x | F ((PoissonPP.inWindow (boundaryWindow K a b T n) (PoissonPP.config x)).map
      (boundaryMark K a b T n))}
  let qt := fun F : Multiset (Pt m) → Prop =>
    (PoissonPP.law (ENNReal.ofReal A⁻¹ • trimmedIntensity a b T)).real
    {ω | F (PoissonPP.config ω.2)}
  have htrimerr := polygon_trimmed_uniform_event_error hm hv harea a b ha hab hb hT
    (ε / 4) (by positivity)
  have hendpoint : ∀ᶠ n : ℕ in atTop,
      (Measure.pi fun _ : Fin n => polygonSample v hm hv harea).real
        (endpointHit K δ T n) < ε / 4 := by
    have ht : Tendsto (fun n : ℕ => (2 * (m : ℝ) * δ * T + C * T * (T / n)) / A)
        atTop (𝓝 (2 * (m : ℝ) * δ * T / A)) := by
      simpa using (tendsto_const_nhds.add
        ((tendsto_const_div_atTop_nhds_zero_nat T).const_mul (C * T))).div_const A
    have hrate : 2 * (m : ℝ) * δ * T / A < ε / 4 := by linarith [hgood.2]
    filter_upwards [ht.eventually (Iio_mem_nhds hrate), eventually_gt_atTop 0] with n hn hnpos
    exact (hbound δ hδ.le T hT.le n hnpos).trans_lt hn
  have hcorner : ∀ᶠ n : ℕ in atTop,
      (Measure.pi fun _ : Fin n => polygonSample v hm hv harea).real
        {x | ∃ j, x j ∈ cornerOverlap K (T / n)} < ε / 4 := by
    have ht := (ENNReal.tendsto_toReal (by simp : (0 : ℝ≥0∞) ≠ ⊤)).comp
      (cornerOverlap_hit_limit_zero hm hv harea hT.le)
    have ht' : Tendsto (fun n : ℕ => (Measure.pi fun _ : Fin n => polygonSample v hm hv harea).real
        {x | ∃ j, x j ∈ cornerOverlap K (T / n)}) atTop (𝓝 0) := by
      simpa only [Function.comp_def, measureReal_def, ENNReal.toReal_zero, K] using ht
    exact ht'.eventually (Iio_mem_nhds (by positivity))
  filter_upwards [physical_trimmed_event_uniform_bound hm hv harea hδ
    (fun i => (hab i).le) hT.le, hendpoint, hcorner, htrimerr]
      with n hdiff hend hcorn htrim F hF
  have hpoisson : |qt F - q F| < ε / 8 := by
    rw [abs_sub_comm]
    exact (poisson_trimmed_event_diff_le hm hv harea hδ.le
      (fun i => (hab i).le) hT.le F hF).trans_lt hgood.2
  have htri : |p F n - q F| ≤ |p F n - pt F n| + |pt F n - qt F| + |qt F - q F| := by
    calc _ ≤ |p F n - pt F n| + |pt F n - q F| := abs_sub_le _ _ _
         _ ≤ |p F n - pt F n| + (|pt F n - qt F| + |qt F - q F|) :=
           add_le_add le_rfl (abs_sub_le _ _ _)
         _ = _ := by ring
  have hd := hdiff F
  have ht := htrim F hF
  change |p F n - pt F n| ≤ _ at hd
  change |pt F n - qt F| < ε / 4 at ht
  linarith

/-- Normalized version with exactly the paper's intensity. -/
theorem polygon_boundary_uniform_error (hm : 3 ≤ m) (hv : ConvexPos v)
    (harea : area v = 1) {T : ℝ} (hT : 0 < T) :
    let K := sidesOf v hm hv harea
    ∀ ε > 0, ∀ᶠ n : ℕ in atTop, ∀ F : Multiset (Pt m) → Prop,
      (∀ k, MeasurableSet {x : Fin k → Pt m | F (PoissonPP.config x)}) →
      |(Measure.pi fun _ : Fin n => polygonSample v hm hv harea).real
        {x | F ((PoissonPP.inWindow (physicalBoundaryWindow K T n)
          (PoissonPP.config x)).map (physicalBoundaryMark K T n))} -
        (PoissonPP.law (Λ K T)).real {ω | F (PoissonPP.config ω.2)}| < ε := by
  have h := polygon_full_boundary_uniform_error hm hv harea hT
  simpa only [polygonRegion_volume_one hm hv harea, ENNReal.toReal_one, inv_one,
    ENNReal.ofReal_one, one_smul] using h

end Enclosing
