import EnclosingCopy.Enclosing.EndpointMass
import EnclosingCopy.Poisson.EventComparison

/-!
# Endpoint omissions are uniformly negligible for iid polygon samples

At depth `T/n`, the chance of hitting an omitted endpoint region is at most a
constant times the trim margin plus a term tending to zero. Consequently the
margin can be chosen before the sample size, with no event-continuity assumption.
-/
namespace Enclosing
open MeasureTheory Set Filter Topology
variable {m : ℕ} [NeZero m] {v : Fin m → ℝ × ℝ}

/-- A finite sample contains a point omitted by endpoint trimming. -/
def endpointHit (K : Sides m) (δ T : ℝ) (n : ℕ) : Set (Fin n → ℝ × ℝ) :=
  {x | ∃ i, x i ∈ omittedBoundary K δ (T / n)}

omit [NeZero m] in
lemma measurableSet_endpointHit (K : Sides m) (δ T : ℝ) (n : ℕ) :
    MeasurableSet (endpointHit K δ T n) := by
  have he : endpointHit K δ T n = ⋃ i : Fin n,
      (Function.eval i) ⁻¹' omittedBoundary K δ (T / n) := by ext x; simp [endpointHit]
  rw [he]
  exact MeasurableSet.iUnion fun i =>
    (measurableSet_omittedBoundary K δ _).preimage (measurable_pi_apply i)

/-- A uniform finite-sample error bound with explicit order of the margin and depth. -/
theorem exists_endpointHit_bound (hm : 3 ≤ m) (hv : ConvexPos v) (harea : area v = 1) :
    let K := sidesOf v hm hv harea
    ∃ C ≥ 0, ∀ δ ≥ 0, ∀ T ≥ 0, ∀ n : ℕ, 0 < n →
      (Measure.pi fun _ : Fin n => polygonSample v hm hv harea).real (endpointHit K δ T n) ≤
        (2 * (m : ℝ) * δ * T + C * T * (T / n)) /
          (volume (polygonRegion K)).toReal := by
  intro K
  obtain ⟨C, hC, hbound⟩ := exists_omittedBoundary_mass_bound hm hv harea
  refine ⟨C, hC, ?_⟩
  intro δ hδ T hT n hn
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hb := mul_le_mul_of_nonneg_left (hbound δ hδ (T / n) (div_nonneg hT hn'.le)) hn'.le
  have hi := PoissonPP.iid_hit_real_le (polygonSample v hm hv harea)
    (measurableSet_omittedBoundary K δ (T / n)) n
  apply hi.trans
  convert hb using 1
  field_simp
  ring

/-- **Endpoint trimming tightness.** Choose a positive admissible margin first;
then every sufficiently large iid sample avoids the omitted regions with probability
at least `1-ε`. -/
theorem polygon_endpoint_trimming_tightness (hm : 3 ≤ m) (hv : ConvexPos v)
    (harea : area v = 1) {T : ℝ} (hT : 0 ≤ T) {ε : ℝ} (hε : 0 < ε) :
    let K := sidesOf v hm hv harea
    ∃ δ > 0, (∀ i, K.a i + δ < K.b i - δ) ∧
      ∀ᶠ n : ℕ in atTop,
        (Measure.pi fun _ : Fin n => polygonSample v hm hv harea).real
          (endpointHit K δ T n) < ε := by
  intro K
  obtain ⟨C, _, hbound⟩ := exists_endpointHit_bound hm hv harea
  let A := (volume (polygonRegion K)).toReal
  have htrim : ∀ᶠ δ : ℝ in 𝓝 0, ∀ i : Fin m, K.a i + δ < K.b i - δ := by
    apply eventually_all.mpr
    intro i
    have hc : Continuous (fun δ : ℝ => K.a i + δ - (K.b i - δ)) := by fun_prop
    have hz : K.a i + 0 - (K.b i - 0) < 0 := by simpa using sub_neg.mpr (K.hab i)
    exact ((hc.tendsto 0).eventually (Iio_mem_nhds hz)).mono fun δ hδ => by linarith
  have hsmall : ∀ᶠ δ : ℝ in 𝓝 0, (2 * (m : ℝ) * δ * T) / A < ε / 2 := by
    have hc : Continuous (fun δ : ℝ => (2 * (m : ℝ) * δ * T) / A) := by fun_prop
    have hz : (2 * (m : ℝ) * (0 : ℝ) * T) / A < ε / 2 := by simpa using half_pos hε
    exact (hc.tendsto 0).eventually (Iio_mem_nhds hz)
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp (htrim.and hsmall)
  let δ := r / 2
  have hδ : 0 < δ := half_pos hr
  have hδr : dist δ 0 < r := by rw [Real.dist_eq, sub_zero, abs_of_pos hδ]; dsimp [δ]; linarith
  have hgood := hball hδr
  refine ⟨δ, hδ, hgood.1, ?_⟩
  have ht : Tendsto (fun n : ℕ =>
      (2 * (m : ℝ) * δ * T + C * T * (T / n)) / A) atTop
      (𝓝 ((2 * (m : ℝ) * δ * T) / A)) := by
    simpa using (tendsto_const_nhds.add
      ((tendsto_const_div_atTop_nhds_zero_nat T).const_mul (C * T))).div_const A
  have hrate : (2 * (m : ℝ) * δ * T) / A < ε := hgood.2.trans (half_lt_self hε)
  filter_upwards [ht.eventually (Iio_mem_nhds hrate), eventually_gt_atTop 0] with n hn hnpos
  exact (hbound δ hδ.le T hT n hnpos).trans_lt hn

/-- The extra corner projections outside the untrimmed side intervals vanish even
with no positive endpoint margin. -/
theorem endpoint_protrusion_hit_limit_zero (hm : 3 ≤ m) (hv : ConvexPos v)
    (harea : area v = 1) {T : ℝ} (hT : 0 ≤ T) :
    let K := sidesOf v hm hv harea
    Tendsto (fun n : ℕ => (Measure.pi fun _ : Fin n => polygonSample v hm hv harea).real
      (endpointHit K 0 T n)) atTop (𝓝 0) := by
  intro K
  obtain ⟨C, _, hbound⟩ := exists_endpointHit_bound hm hv harea
  have ht : Tendsto (fun n : ℕ =>
      (C * T * (T / n)) / (volume (polygonRegion K)).toReal) atTop (𝓝 0) := by
    simpa using ((tendsto_const_div_atTop_nhds_zero_nat T).const_mul (C * T)).div_const _
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds ht
    (Eventually.of_forall fun _ => measureReal_nonneg)
  filter_upwards [eventually_gt_atTop 0] with n hn
  simpa using hbound 0 le_rfl T hT n hn

end Enclosing
