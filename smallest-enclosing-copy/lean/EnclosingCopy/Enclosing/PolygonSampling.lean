import EnclosingCopy.Enclosing.PolygonWindows

/-!
# Uniform iid sampling in the physical polygon and witness-window limits

The actual supporting-half-plane region has finite positive Lebesgue area. Its
normalized restriction is therefore a genuine probability law. A trimmed side
rectangle at depth `y/n` has scaled probability `(b-a)y/area`, and the probability
that an iid sample misses it tends to the corresponding exponential. The area
here is the actual Lebesgue area; no equality with shoelace area is assumed.
-/
namespace Enclosing
open MeasureTheory Set Filter Topology
open scoped NNReal
variable {m : ℕ} [NeZero m] {v : Fin m → ℝ × ℝ}

/-- A genuine convex polygon's physical region has positive area. -/
theorem polygonRegion_volume_pos (hm : 3 ≤ m) (hv : ConvexPos v) (harea : area v = 1) :
    0 < volume (polygonRegion (sidesOf v hm hv harea)) := by
  let K := sidesOf v hm hv harea
  let i : Fin m := 0
  let L := K.b i - K.a i
  have hL : 0 < L := sub_pos.mpr (K.hab i)
  let a := K.a i + L / 3
  let b := K.b i - L / 3
  have ha : K.a i < a := by dsimp [a]; linarith
  have hab : a < b := by dsimp [a, b, L] at *; linarith
  have hb : b < K.b i := by dsimp [b]; linarith
  obtain ⟨d, hd, hW⟩ := exists_sideWindow_subset hm hv harea i ha hab.le hb
  have hsub := hW d ⟨hd.le, le_rfl⟩
  have hvol : 0 < volume (sideWindow K i a b d) := by
    rw [sideWindow_volume K (goodSides_of_convex hm hv harea)]
    have : 0 < b - a := sub_pos.mpr hab
    positivity
  exact hvol.trans_le (measure_mono hsub)

/-- Uniform planar sampling in the polygon, using its actual Lebesgue area. -/
noncomputable def polygonSample (v : Fin m → ℝ × ℝ) (hm : 3 ≤ m)
    (hv : ConvexPos v) (harea : area v = 1) : Measure (ℝ × ℝ) :=
  ProbabilityTheory.cond volume (polygonRegion (sidesOf v hm hv harea))

instance polygonSample_probability (v : Fin m → ℝ × ℝ) (hm : 3 ≤ m)
    (hv : ConvexPos v) (harea : area v = 1) :
    IsProbabilityMeasure (polygonSample v hm hv harea) :=
  ProbabilityTheory.cond_isProbabilityMeasure_of_finite
    (polygonRegion_volume_pos hm hv harea).ne'
    (polygonRegion_volume_ne_top _ (goodSides_of_convex hm hv harea))

/-- The area denominator used by the physical uniform law is strictly positive. -/
lemma physical_area_pos (hm : 3 ≤ m) (hv : ConvexPos v) (harea : area v = 1) :
    0 < (volume (polygonRegion (sidesOf v hm hv harea))).toReal :=
  ENNReal.toReal_pos (polygonRegion_volume_pos hm hv harea).ne'
    (polygonRegion_volume_ne_top _ (goodSides_of_convex hm hv harea))

/-- Exact probability of a side rectangle contained in the physical polygon. -/
theorem polygonSample_sideWindow (hm : 3 ≤ m) (hv : ConvexPos v) (harea : area v = 1)
    (i : Fin m) {a b d : ℝ} (hab : a ≤ b) (hd : 0 ≤ d)
    (hsub : sideWindow (sidesOf v hm hv harea) i a b d ⊆
      polygonRegion (sidesOf v hm hv harea)) :
    (polygonSample v hm hv harea).real (sideWindow (sidesOf v hm hv harea) i a b d) =
      (b - a) * d / (volume (polygonRegion (sidesOf v hm hv harea))).toReal := by
  rw [measureReal_def, polygonSample, ProbabilityTheory.cond_apply
    (measurableSet_polygonRegion _), inter_eq_right.mpr hsub,
    sideWindow_volume _ (goodSides_of_convex hm hv harea)]
  rw [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (sub_nonneg.mpr hab), ENNReal.toReal_ofReal hd]
  ring

/-- The scaled witness-window mass is eventually exactly its constant geometric rate. -/
theorem sideWindow_scaled_mass (hm : 3 ≤ m) (hv : ConvexPos v) (harea : area v = 1)
    (i : Fin m) {a b : ℝ} (ha : aEnd v i < a) (hab : a ≤ b) (hb : b < bEnd v i)
    {y : ℝ} (hy : 0 ≤ y) :
    let K := sidesOf v hm hv harea
    ∀ᶠ n : ℕ in atTop, (n : ℝ) *
      (polygonSample v hm hv harea).real (sideWindow K i a b (y / n)) =
        (b - a) * y / (volume (polygonRegion K)).toReal := by
  intro K
  obtain ⟨d₀, hd₀, hsub⟩ := exists_sideWindow_subset hm hv harea i ha hab hb
  have hsmall := (tendsto_const_div_atTop_nhds_zero_nat y).eventually (Iio_mem_nhds hd₀)
  filter_upwards [hsmall, eventually_gt_atTop 0] with n hn hnpos
  have hn' : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hyd : 0 ≤ y / (n : ℝ) := div_nonneg hy hn'.le
  rw [polygonSample_sideWindow hm hv harea i hab hyd (hsub _ ⟨hyd, hn.le⟩)]
  dsimp [K]
  field_simp

/-- **Witness-window limit for actual uniform iid polygon samples.** -/
theorem sideWindow_void_limit (hm : 3 ≤ m) (hv : ConvexPos v) (harea : area v = 1)
    (i : Fin m) {a b : ℝ} (ha : aEnd v i < a) (hab : a ≤ b) (hb : b < bEnd v i)
    {y : ℝ} (hy : 0 ≤ y) :
    let K := sidesOf v hm hv harea
    Tendsto (fun n : ℕ => (Measure.pi fun _ : Fin n => polygonSample v hm hv harea)
      {x | ∀ j, x j ∉ sideWindow K i a b (y / n)}) atTop
      (𝓝 (ENNReal.ofReal (Real.exp (-((b - a) * y /
        (volume (polygonRegion K)).toReal))))) := by
  intro K
  let r : ℝ≥0 := ⟨(b - a) * y / (volume (polygonRegion K)).toReal,
    div_nonneg (mul_nonneg (sub_nonneg.mpr hab) hy) (physical_area_pos hm hv harea).le⟩
  have he : (fun n : ℕ => (n : ℝ) * (polygonSample v hm hv harea).real
      (sideWindow K i a b (y / n))) =ᶠ[atTop] (fun _ => (r : ℝ)) :=
    sideWindow_scaled_mass hm hv harea i ha hab hb hy
  have hr : Tendsto (fun n : ℕ => (n : ℝ) * (polygonSample v hm hv harea).real
      (sideWindow K i a b (y / n))) atTop (𝓝 (r : ℝ)) :=
    tendsto_const_nhds.congr' he.symm
  exact PoissonPP.iid_void_limit (fun _ => polygonSample v hm hv harea)
    (fun n : ℕ => sideWindow K i a b (y / n))
    (fun n => measurableSet_sideWindow K i a b _) hr

end Enclosing
