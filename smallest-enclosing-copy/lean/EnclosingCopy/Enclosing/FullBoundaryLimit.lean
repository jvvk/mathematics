import EnclosingCopy.Enclosing.PhysicalBoundary
import EnclosingCopy.Enclosing.BoundaryIntensityComparison

/-!
# The full marked boundary Poisson limit for actual polygon samples

Endpoint margins are removed by probability bounds on both the physical and
Poisson sides. At each fixed positive depth cutoff, every measurable configuration
event converges, without any continuity hypothesis on that event.
-/
namespace Enclosing
open MeasureTheory Set Filter Topology
open scoped ENNReal
variable {m : ℕ} [NeZero m] {v : Fin m → ℝ × ℝ}

/-- **Full boundary-window Poisson limit for actual uniform iid polygon samples.**
The observation includes all physical side-depth strips, including corner projections;
ambiguous side labels are selected measurably and disappear with high probability.
The cutoff remains fixed, and the intensity uses actual physical area `A`.
-/
theorem polygon_full_boundary_event_limit (hm : 3 ≤ m) (hv : ConvexPos v)
    (harea : area v = 1) {T : ℝ} (hT : 0 < T) (F : Multiset (Pt m) → Prop)
    (hF : ∀ k, MeasurableSet {x : Fin k → Pt m | F (PoissonPP.config x)}) :
    let K := sidesOf v hm hv harea
    let A := (volume (polygonRegion K)).toReal
    Tendsto (fun n : ℕ => (Measure.pi fun _ : Fin n => polygonSample v hm hv harea).real
      {x | F ((PoissonPP.inWindow (physicalBoundaryWindow K T n) (PoissonPP.config x)).map
        (physicalBoundaryMark K T n))}) atTop
      (𝓝 ((PoissonPP.law (ENNReal.ofReal A⁻¹ • Λ K T)).real
        {ω | F (PoissonPP.config ω.2)})) := by
  intro K A
  let p := fun n : ℕ => (Measure.pi fun _ : Fin n => polygonSample v hm hv harea).real
    {x | F ((PoissonPP.inWindow (physicalBoundaryWindow K T n) (PoissonPP.config x)).map
      (physicalBoundaryMark K T n))}
  let q := (PoissonPP.law (ENNReal.ofReal A⁻¹ • Λ K T)).real {ω | F (PoissonPP.config ω.2)}
  change Tendsto p atTop (𝓝 q)
  apply Metric.tendsto_atTop.mpr
  intro ε hε
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
  let pt := fun n : ℕ => (Measure.pi fun _ : Fin n => polygonSample v hm hv harea).real
    {x | F ((PoissonPP.inWindow (boundaryWindow K a b T n) (PoissonPP.config x)).map
      (boundaryMark K a b T n))}
  let qt := (PoissonPP.law (ENNReal.ofReal A⁻¹ • trimmedIntensity a b T)).real
    {ω | F (PoissonPP.config ω.2)}
  have htrimlim : Tendsto pt atTop (𝓝 qt) :=
    polygon_trimmed_event_limit hm hv harea a b ha hab hb hT F hF
  have htrimerr : ∀ᶠ n : ℕ in atTop, |pt n - qt| < ε / 4 := by
    have ht : Tendsto (fun n => |pt n - qt|) atTop (𝓝 0) := by
      simpa using (htrimlim.sub_const qt).abs
    exact ht.eventually (Iio_mem_nhds (by positivity))
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
  have hpoisson : |qt - q| < ε / 8 := by
    rw [abs_sub_comm]
    exact (poisson_trimmed_event_diff_le hm hv harea hδ.le
      (fun i => (hab i).le) hT.le F hF).trans_lt hgood.2
  have hall : ∀ᶠ n : ℕ in atTop, dist (p n) q < ε := by
    filter_upwards [physical_trimmed_event_diff_le hm hv harea hδ (fun i => (hab i).le)
      hT.le F, hendpoint, hcorner, htrimerr] with n hdiff hend hcorn htrim
    rw [Real.dist_eq]
    have htri : |p n - q| ≤ |p n - pt n| + |pt n - qt| + |qt - q| := by
      calc _ ≤ |p n - pt n| + |pt n - q| := abs_sub_le (p n) (pt n) q
           _ ≤ |p n - pt n| + (|pt n - qt| + |qt - q|) :=
             add_le_add le_rfl (abs_sub_le (pt n) qt q)
           _ = _ := by ring
    change |p n - pt n| ≤ _ at hdiff
    linarith
  exact eventually_atTop.mp hall

end Enclosing
