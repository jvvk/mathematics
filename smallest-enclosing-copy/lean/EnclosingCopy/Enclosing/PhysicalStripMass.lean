import EnclosingCopy.Enclosing.EndpointMass

/-!
# First-order area of a full physical side strip

The enlarged rectangle supplies an upper bound. Every fixed positive trim margin
supplies the matching lower bound, and that margin may then approach zero.
-/
namespace Enclosing
open MeasureTheory Set Filter Topology
variable {m : ℕ} [NeZero m] {v : Fin m → ℝ × ℝ}

theorem exists_physicalSideStrip_mass_bound (hm : 3 ≤ m) (hv : ConvexPos v)
    (harea : area v = 1) (i : Fin m) :
    let K := sidesOf v hm hv harea
    ∃ C ≥ 0, ∀ d ≥ 0,
      (polygonSample v hm hv harea).real (physicalSideStrip K i d) ≤
        ((K.b i - K.a i) + 2 * C * d) * d / (volume (polygonRegion K)).toReal := by
  intro K
  obtain ⟨C, hC, hsub⟩ := exists_physicalSideStrip_enlargement hm hv harea i
  refine ⟨C, hC, ?_⟩
  intro d hd
  have hwidth : 0 ≤ K.b i + C * d - (K.a i - C * d) := by
    nlinarith [K.hab i, mul_nonneg hC hd]
  have hle := measureReal_mono (μ := volume) (hsub d hd)
    (isCompact_sideWindow K i _ _ d).measure_ne_top
  simp only [measureReal_def] at hle
  change (volume (physicalSideStrip K i d)).toReal ≤
    (volume (sideWindow K i (K.a i - C * d) (K.b i + C * d) d)).toReal at hle
  rw [sideWindow_volume K (goodSides_of_convex hm hv harea),
    ENNReal.toReal_mul, ENNReal.toReal_ofReal hwidth,
    ENNReal.toReal_ofReal hd] at hle
  rw [polygonSample_real_subset hm hv harea
    (S := physicalSideStrip K i d) inter_subset_left]
  apply div_le_div_of_nonneg_right _ (physical_area_pos hm hv harea).le
  have he : K.b i + C * d - (K.a i - C * d) = K.b i - K.a i + 2 * C * d := by ring
  simpa only [he, measureReal_def] using hle

/-- Full physical strip masses, including endpoint projections, have the expected rate. -/
theorem physicalSideStrip_scaled_mass (hm : 3 ≤ m) (hv : ConvexPos v)
    (harea : area v = 1) (i : Fin m) {y : ℝ} (hy : 0 ≤ y) :
    let K := sidesOf v hm hv harea
    Tendsto (fun n : ℕ => (n : ℝ) * (polygonSample v hm hv harea).real
      (physicalSideStrip K i (y / n))) atTop
      (𝓝 ((K.b i - K.a i) * y / (volume (polygonRegion K)).toReal)) := by
  intro K
  let A := (volume (polygonRegion K)).toReal
  let r := (K.b i - K.a i) * y / A
  let p := fun n : ℕ => (n : ℝ) * (polygonSample v hm hv harea).real
    (physicalSideStrip K i (y / n))
  change Tendsto p atTop (𝓝 r)
  obtain ⟨C, _, hupper⟩ := exists_physicalSideStrip_mass_bound hm hv harea i
  have hub : ∀ᶠ n : ℕ in atTop,
      p n ≤ ((K.b i - K.a i) * y + 2 * C * y * (y / n)) / A := by
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have h := mul_le_mul_of_nonneg_left
      (hupper (y / n) (div_nonneg hy hn'.le)) hn'.le
    convert h using 1
    field_simp
    ring
  have hu : Tendsto (fun n : ℕ =>
      ((K.b i - K.a i) * y + 2 * C * y * (y / n)) / A) atTop (𝓝 r) := by
    simpa [r] using (tendsto_const_nhds.add
      ((tendsto_const_div_atTop_nhds_zero_nat y).const_mul (2 * C * y))).div_const A
  apply tendsto_order.mpr
  constructor
  · intro l hl
    have hmargin : ∀ᶠ δ : ℝ in 𝓝 0,
        K.a i + δ < K.b i - δ ∧ l < (K.b i - δ - (K.a i + δ)) * y / A := by
      have hc : Continuous (fun δ : ℝ => K.a i + δ - (K.b i - δ)) := by fun_prop
      have ht : Continuous (fun δ : ℝ => (K.b i - δ - (K.a i + δ)) * y / A) := by
        fun_prop
      have h₁ : K.a i + 0 - (K.b i - 0) < 0 := by
        simpa using sub_neg.mpr (K.hab i)
      have h₂ : l < (K.b i - 0 - (K.a i + 0)) * y / A := by simpa [r] using hl
      exact (((hc.tendsto 0).eventually (Iio_mem_nhds h₁)).mono
        (fun δ hδ => by linarith)).and ((ht.tendsto 0).eventually (Ioi_mem_nhds h₂))
    obtain ⟨b, hb, hball⟩ := Metric.eventually_nhds_iff.mp hmargin
    let δ := b / 2
    have hδ : 0 < δ := half_pos hb
    have hd : dist δ 0 < b := by
      rw [Real.dist_eq, sub_zero, abs_of_pos hδ]; dsimp [δ]; linarith
    have hgood := hball hd
    have ha : aEnd v i < K.a i + δ := lt_add_of_pos_right _ hδ
    have hb' : K.b i - δ < bEnd v i := sub_lt_self _ hδ
    obtain ⟨d₀, hd₀, hsub⟩ := exists_sideWindow_subset hm hv harea i ha hgood.1.le hb'
    filter_upwards [sideWindow_scaled_mass hm hv harea i ha hgood.1.le hb' hy,
      (tendsto_const_div_atTop_nhds_zero_nat y).eventually (Iio_mem_nhds hd₀)]
      with n he hn
    have hW := hsub _ ⟨div_nonneg hy (Nat.cast_nonneg n), hn.le⟩
    have hstrip : sideWindow K i (K.a i + δ) (K.b i - δ) (y / n) ⊆
        physicalSideStrip K i (y / n) := by
      intro x hx
      refine ⟨hW hx, ?_⟩
      obtain ⟨q, hq, rfl⟩ := hx
      have hc := congrArg Prod.snd (sideCoords_chart (K.u i)
        ((goodSides_of_convex hm hv harea).unit i) (K.h i) q)
      change K.h i - dot (sideChart (K.u i) (K.h i) q) (K.u i) = q.2 at hc
      change K.h i - dot (sideChart (K.u i) (K.h i) q) (K.u i) ∈ Icc 0 (y / n)
      rw [hc]; exact hq.2
    have hmono := mul_le_mul_of_nonneg_left
      (measureReal_mono (μ := polygonSample v hm hv harea) hstrip) (Nat.cast_nonneg n)
    rw [he] at hmono
    exact hgood.2.trans_le hmono
  · intro u hu'
    filter_upwards [hub, hu.eventually (Iio_mem_nhds hu')] with n hn hn'
    exact hn.trans_lt hn'

/-- The normalization cancels: scaled physical strip areas tend to length times depth. -/
theorem physicalSideStrip_scaled_volume (hm : 3 ≤ m) (hv : ConvexPos v)
    (harea : area v = 1) (i : Fin m) {y : ℝ} (hy : 0 ≤ y) :
    let K := sidesOf v hm hv harea
    Tendsto (fun n : ℕ => (n : ℝ) * volume.real (physicalSideStrip K i (y / n)))
      atTop (𝓝 ((K.b i - K.a i) * y)) := by
  intro K
  let A := (volume (polygonRegion K)).toReal
  have hA : A ≠ 0 := (physical_area_pos hm hv harea).ne'
  have h := (physicalSideStrip_scaled_mass hm hv harea i hy).const_mul A
  convert h using 1
  · funext n
    rw [polygonSample_real_subset hm hv harea
      (S := physicalSideStrip (sidesOf v hm hv harea) i (y / n)) inter_subset_left]
    change (n : ℝ) * volume.real (physicalSideStrip K i (y / n)) =
      A * ((n : ℝ) * (volume.real (physicalSideStrip K i (y / n)) / A))
    field_simp
  · congr 1
    change (K.b i - K.a i) * y = A * ((K.b i - K.a i) * y / A)
    field_simp

end Enclosing
