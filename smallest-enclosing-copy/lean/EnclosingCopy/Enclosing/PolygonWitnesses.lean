import EnclosingCopy.Enclosing.PolygonOverlap

/-!
# Simultaneous shallow witnesses for actual polygon samples

Any finite family of positive-length trimmed side intervals has sample witnesses at
depth at most `y/n`, with arbitrarily high probability for sufficiently large fixed
`y` and then sufficiently large `n`. The order of these quantifiers is explicit.
-/
namespace Enclosing
open MeasureTheory Set Filter Topology
variable {m : ℕ} [NeZero m] {v : Fin m → ℝ × ℝ}
variable {ι : Type*} [Fintype ι]

/-- A finite family fails if one of its windows has no sample point. -/
def witnessFailure (K : Sides m) (i : ι → Fin m) (a b : ι → ℝ) (n : ℕ) (y : ℝ) :
    Set (Fin n → ℝ × ℝ) := {x | ∃ t, ∀ j, x j ∉ sideWindow K (i t) (a t) (b t) (y / n)}

omit [NeZero m] in
/-- Finite-family witness failure is bounded by the sum of its individual void probabilities. -/
theorem witnessFailure_le (μ : Measure (ℝ × ℝ)) [IsProbabilityMeasure μ]
    (K : Sides m) (i : ι → Fin m) (a b : ι → ℝ) (n : ℕ) (y : ℝ) :
    (Measure.pi fun _ : Fin n => μ).real (witnessFailure K i a b n y) ≤
      ∑ t, (Measure.pi fun _ : Fin n => μ).real
        {x | ∀ j, x j ∉ sideWindow K (i t) (a t) (b t) (y / n)} := by
  have he : witnessFailure K i a b n y =
      ⋃ t, {x : Fin n → ℝ × ℝ | ∀ j, x j ∉ sideWindow K (i t) (a t) (b t) (y / n)} := by
    ext; simp [witnessFailure]
  rw [he]
  exact measureReal_iUnion_fintype_le _

/-- The asymptotic finite-family union bound tends to zero as the depth cutoff grows. -/
theorem witness_exponential_sum_zero (hm : 3 ≤ m) (hv : ConvexPos v) (harea : area v = 1)
    (a b : ι → ℝ) (hab : ∀ t, a t < b t) :
    let A := (volume (polygonRegion (sidesOf v hm hv harea))).toReal
    Tendsto (fun y : ℝ => ∑ t, Real.exp (-((b t - a t) * y / A))) atTop (𝓝 0) := by
  intro A
  have ht (t : ι) : Tendsto (fun y : ℝ => Real.exp (-((b t - a t) * y / A)))
      atTop (𝓝 0) := by
    have hc : 0 < (b t - a t) / A := div_pos (sub_pos.mpr (hab t)) (physical_area_pos hm hv harea)
    have he := Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.const_mul_atTop hc)
    convert he using 1
    funext y
    congr 1
    simp only [id_eq]
    ring
  simpa using tendsto_finsetSum Finset.univ (fun t _ => ht t)

omit [Fintype ι] in
/-- **Simultaneous witness tightness for actual fixed-size uniform samples.** -/
theorem polygon_witness_tightness [Finite ι] (hm : 3 ≤ m) (hv : ConvexPos v) (harea : area v = 1)
    (i : ι → Fin m) (a b : ι → ℝ) (ha : ∀ t, aEnd v (i t) < a t)
    (hab : ∀ t, a t < b t) (hb : ∀ t, b t < bEnd v (i t)) :
    let K := sidesOf v hm hv harea
    ∀ ε > 0, ∃ y > 0, ∀ᶠ n : ℕ in atTop,
      (Measure.pi fun _ : Fin n => polygonSample v hm hv harea).real
        (witnessFailure K i a b n y) < ε := by
  classical
  let _ := Fintype.ofFinite ι
  intro K ε hε
  let A := (volume (polygonRegion K)).toReal
  have hylarge := (witness_exponential_sum_zero hm hv harea a b hab).eventually
    (Iio_mem_nhds (show 0 < ε / 2 by linarith))
  obtain ⟨y, hy, hysum⟩ := ((eventually_gt_atTop 0).and hylarge).exists
  refine ⟨y, hy, ?_⟩
  have hvoid (t : ι) : Tendsto (fun n : ℕ =>
      (Measure.pi fun _ : Fin n => polygonSample v hm hv harea).real
        {x | ∀ j, x j ∉ sideWindow K (i t) (a t) (b t) (y / n)}) atTop
      (𝓝 (Real.exp (-((b t - a t) * y / A)))) := by
    have ht := (ENNReal.tendsto_toReal ENNReal.ofReal_ne_top).comp
      (sideWindow_void_limit hm hv harea (i t) (ha t) (hab t).le (hb t) hy.le)
    simpa only [measureReal_def, ENNReal.toReal_ofReal (Real.exp_pos _).le,
      Function.comp_def, A, K] using ht
  have hsum : Tendsto (fun n : ℕ => ∑ t,
      (Measure.pi fun _ : Fin n => polygonSample v hm hv harea).real
        {x | ∀ j, x j ∉ sideWindow K (i t) (a t) (b t) (y / n)}) atTop
      (𝓝 (∑ t, Real.exp (-((b t - a t) * y / A)))) :=
    tendsto_finsetSum Finset.univ (fun t _ => hvoid t)
  have hsumε : ∑ t, Real.exp (-((b t - a t) * y / A)) < ε := by
    exact hysum.trans (by linarith)
  filter_upwards [hsum.eventually (Iio_mem_nhds hsumε)] with n hn
  exact (witnessFailure_le (polygonSample v hm hv harea) K i a b n y).trans_lt hn

end Enclosing
