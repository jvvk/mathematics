import EnclosingCopy.Enclosing.PolygonSampling

/-!
# Vanishing corner overlaps for uniform polygon samples

Two nonparallel depth strips have area proportional to the product of their depths.
Distinct parallel supporting sides have positive width, so sufficiently thin strips
do not meet. These geometric estimates remove corner overlaps from iid samples.
-/
namespace Enclosing
open MeasureTheory Set Filter Topology Matrix

/-- The two inward depths at a pair of supporting lines. -/
def doubleDepth (u w : ℝ × ℝ) (h k : ℝ) (x : ℝ × ℝ) : ℝ × ℝ :=
  (h - dot x u, k - dot x w)

lemma continuous_doubleDepth (u w : ℝ × ℝ) (h k : ℝ) :
    Continuous (doubleDepth u w h k) := by unfold doubleDepth dot; fun_prop

/-- The two-depth map rescales planar Lebesgue measure by the inverse cross product. -/
theorem doubleDepth_map_volume (u w : ℝ × ℝ) (h k : ℝ) (huw : cross u w ≠ 0) :
    Measure.map (doubleDepth u w h k) volume = ENNReal.ofReal |cross u w|⁻¹ • volume := by
  let A : Matrix (Fin 2) (Fin 2) ℝ := !![-u.1, -u.2; -w.1, -w.2]
  have hdet : A.det = cross u w := by simp [A, Matrix.det_fin_two, cross]
  have hA : Measurable (Matrix.toLin' A) := (LinearMap.continuous_on_pi _).measurable
  let e := MeasurableEquiv.piFinTwo (fun _ : Fin 2 => ℝ)
  have he : MeasurePreserving e volume volume := volume_preserving_piFinTwo _
  let f := e ∘ Matrix.toLin' A ∘ e.symm
  have hf : Measurable f := he.measurable.comp (hA.comp he.symm.measurable)
  have hmap : Measure.map f volume = ENNReal.ofReal |cross u w|⁻¹ • volume := by
    rw [show f = e ∘ (Matrix.toLin' A ∘ e.symm) from rfl,
      ← Measure.map_map he.measurable (hA.comp he.symm.measurable),
      ← Measure.map_map hA he.symm.measurable, he.symm.map_eq,
      Real.map_matrix_volume_pi_eq_smul_volume_pi (by rwa [hdet]), hdet,
      Measure.map_smul, he.map_eq, abs_inv]
    exact he.measurable.aemeasurable
  have hadd := measurePreserving_add_left (volume : Measure (ℝ × ℝ)) (h, k)
  have heq : doubleDepth u w h k = (fun x => (h, k) + x) ∘ f := by
    funext x
    apply Prod.ext <;> simp [doubleDepth, dot, f, e, A, Matrix.toLin'_apply,
      Function.comp_def, MeasurableEquiv.piFinTwo] <;> ring
  rw [heq, ← Measure.map_map hadd.measurable hf, hmap, Measure.map_smul, hadd.map_eq]
  exact hadd.measurable.aemeasurable

/-- Exact area of the intersection of two nonparallel strips, without polygon clipping. -/
theorem doubleDepth_rectangle_volume (u w : ℝ × ℝ) (h k d e : ℝ)
    (huw : cross u w ≠ 0) :
    volume (doubleDepth u w h k ⁻¹' (Icc 0 d ×ˢ Icc 0 e)) =
      ENNReal.ofReal |cross u w|⁻¹ * (ENNReal.ofReal d * ENNReal.ofReal e) := by
  rw [← Measure.map_apply (continuous_doubleDepth u w h k).measurable
    (measurableSet_Icc.prod measurableSet_Icc), doubleDepth_map_volume u w h k huw,
    Measure.smul_apply, smul_eq_mul, Measure.volume_eq_prod, Measure.prod_prod,
    Real.volume_Icc, Real.volume_Icc, sub_zero, sub_zero]

variable {m : ℕ} (K : Sides m)

/-- Points of the polygon within depth `d` of both sides. -/
def sideOverlap (i j : Fin m) (d : ℝ) : Set (ℝ × ℝ) :=
  polygonRegion K ∩ doubleDepth (K.u i) (K.u j) (K.h i) (K.h j) ⁻¹'
    (Icc 0 d ×ˢ Icc 0 d)

lemma measurableSet_sideOverlap (i j : Fin m) (d : ℝ) : MeasurableSet (sideOverlap K i j d) :=
  (measurableSet_polygonRegion K).inter ((measurableSet_Icc.prod measurableSet_Icc).preimage
    (continuous_doubleDepth _ _ _ _).measurable)

lemma sideOverlap_volume_le (i j : Fin m) (d : ℝ) (hij : cross (K.u i) (K.u j) ≠ 0) :
    volume (sideOverlap K i j d) ≤
      ENNReal.ofReal |cross (K.u i) (K.u j)|⁻¹ * (ENNReal.ofReal d * ENNReal.ofReal d) := by
  exact (measure_mono inter_subset_right).trans_eq (doubleDepth_rectangle_volume _ _ _ _ _ _ hij)

/-- Opposite supporting lines cannot both have shallow inward depth. -/
lemma sideOverlap_eq_empty (i j : Fin m) (hij : K.u j = -K.u i) {d : ℝ}
    (hd : 2 * d < K.h i + K.h j) : sideOverlap K i j d = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro x hx
  have h₁ := hx.2.1.2
  have h₂ := hx.2.2.2
  change K.h i - dot x (K.u i) ≤ d at h₁
  change K.h j - dot x (K.u j) ≤ d at h₂
  rw [hij] at h₂
  simp only [dot, Prod.fst_neg, Prod.snd_neg] at h₁ h₂
  linarith

variable [NeZero m] {v : Fin m → ℝ × ℝ}

/-- The normalized overlap mass is at most its unclipped two-strip area divided by area. -/
theorem polygonSample_sideOverlap_le (hm : 3 ≤ m) (hv : ConvexPos v) (harea : area v = 1)
    (i j : Fin m) {d : ℝ} (hd : 0 ≤ d)
    (hij : cross ((sidesOf v hm hv harea).u i) ((sidesOf v hm hv harea).u j) ≠ 0) :
    let K := sidesOf v hm hv harea
    (polygonSample v hm hv harea).real (sideOverlap K i j d) ≤
      (|cross (K.u i) (K.u j)|⁻¹ * (d * d)) / (volume (polygonRegion K)).toReal := by
  intro K
  have hbound := sideOverlap_volume_le K i j d hij
  have hfinite : ENNReal.ofReal |cross (K.u i) (K.u j)|⁻¹ *
      (ENNReal.ofReal d * ENNReal.ofReal d) ≠ ⊤ := by finiteness
  have hr := ENNReal.toReal_mono hfinite hbound
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (inv_nonneg.mpr (abs_nonneg _)),
    ENNReal.toReal_ofReal hd] at hr
  rw [measureReal_def, polygonSample, ProbabilityTheory.cond_apply
    (measurableSet_polygonRegion _), inter_eq_right.mpr
      (show sideOverlap K i j d ⊆ polygonRegion (sidesOf v hm hv harea) from inter_subset_left),
    ENNReal.toReal_mul, ENNReal.toReal_inv]
  dsimp [K] at *
  simpa only [div_eq_mul_inv, mul_comm] using
    mul_le_mul_of_nonneg_right hr (inv_nonneg.mpr (physical_area_pos hm hv harea).le)

/-- Every distinct side-pair overlap has mass `o(1/n)`, including parallel pairs. -/
theorem sideOverlap_scaled_mass_zero (hm : 3 ≤ m) (hv : ConvexPos v) (harea : area v = 1)
    (i j : Fin m) (hij : i ≠ j) {y : ℝ} (hy : 0 ≤ y) :
    let K := sidesOf v hm hv harea
    Tendsto (fun n : ℕ => (n : ℝ) * (polygonSample v hm hv harea).real
      (sideOverlap K i j (y / n))) atTop (𝓝 0) := by
  intro K
  by_cases hcross : cross (K.u i) (K.u j) = 0
  · rcases (goodSides_of_convex hm hv harea).parallel hcross with heq | hop
    · exact (hij heq.symm).elim
    have hw := (goodSides_of_convex hm hv harea).width i j hop
    have ht : Tendsto (fun n : ℕ => 2 * (y / (n : ℝ))) atTop (𝓝 0) := by
      simpa using (tendsto_const_div_atTop_nhds_zero_nat y).const_mul 2
    have he : (fun n : ℕ => (n : ℝ) * (polygonSample v hm hv harea).real
        (sideOverlap K i j (y / n))) =ᶠ[atTop] (fun _ => 0) := by
      filter_upwards [ht.eventually (Iio_mem_nhds hw)] with n hn
      rw [sideOverlap_eq_empty K i j hop hn, measureReal_empty, mul_zero]
    exact tendsto_const_nhds.congr' he.symm
  · let C := |cross (K.u i) (K.u j)|⁻¹ * (y * y) / (volume (polygonRegion K)).toReal
    have hbound : ∀ᶠ n : ℕ in atTop, (n : ℝ) * (polygonSample v hm hv harea).real
        (sideOverlap K i j (y / n)) ≤ C / n := by
      filter_upwards [eventually_gt_atTop 0] with n hn
      have hn' : (0 : ℝ) < n := by exact_mod_cast hn
      have hd : 0 ≤ y / (n : ℝ) := div_nonneg hy hn'.le
      have hb := mul_le_mul_of_nonneg_left
        (polygonSample_sideOverlap_le hm hv harea i j hd hcross) hn'.le
      convert hb using 1
      dsimp [C, K]
      field_simp
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      (tendsto_const_div_atTop_nhds_zero_nat C)
      (Eventually.of_forall (fun _ => mul_nonneg (Nat.cast_nonneg _) measureReal_nonneg)) hbound

/-- All points within depth `d` of at least two distinct sides. -/
def cornerOverlap (d : ℝ) : Set (ℝ × ℝ) :=
  ⋃ i : Fin m, ⋃ j : Fin m, if i = j then ∅ else sideOverlap K i j d

omit [NeZero m] in
lemma measurableSet_cornerOverlap (d : ℝ) : MeasurableSet (cornerOverlap K d) := by
  classical
  apply MeasurableSet.iUnion
  intro i
  apply MeasurableSet.iUnion
  intro j
  split_ifs
  · exact MeasurableSet.empty
  · exact measurableSet_sideOverlap K i j d

/-- The union of every corner overlap still has mass `o(1/n)`. -/
theorem cornerOverlap_scaled_mass_zero (hm : 3 ≤ m) (hv : ConvexPos v) (harea : area v = 1)
    {y : ℝ} (hy : 0 ≤ y) :
    let K := sidesOf v hm hv harea
    Tendsto (fun n : ℕ => (n : ℝ) * (polygonSample v hm hv harea).real
      (cornerOverlap K (y / n))) atTop (𝓝 0) := by
  classical
  intro K
  let B := fun (i j : Fin m) (n : ℕ) => if i = j then ∅ else sideOverlap K i j (y / n)
  have hpair (i j : Fin m) : Tendsto (fun n : ℕ => (n : ℝ) *
      (polygonSample v hm hv harea).real (B i j n)) atTop (𝓝 0) := by
    by_cases hij : i = j
    · simp [B, hij]
    · simpa only [B, ite_eq_right hij] using sideOverlap_scaled_mass_zero hm hv harea i j hij hy
  have hsum : Tendsto (fun n : ℕ => ∑ i : Fin m, ∑ j : Fin m,
      (n : ℝ) * (polygonSample v hm hv harea).real (B i j n)) atTop (𝓝 0) := by
    simpa using tendsto_finsetSum Finset.univ (fun i _ =>
      tendsto_finsetSum Finset.univ (fun j _ => hpair i j))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
    (fun n => mul_nonneg (Nat.cast_nonneg n) measureReal_nonneg)
  intro n
  dsimp only
  simp_rw [← Finset.mul_sum]
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg n)
  calc _ ≤ ∑ i : Fin m, (polygonSample v hm hv harea).real (⋃ j : Fin m, B i j n) :=
      measureReal_iUnion_fintype_le _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro i _
      simpa only [← Finset.mul_sum] using
        measureReal_iUnion_fintype_le (μ := polygonSample v hm hv harea) (B i · n)

/-- **No iid sample lies in a corner overlap with probability tending to one.** -/
theorem cornerOverlap_hit_limit_zero (hm : 3 ≤ m) (hv : ConvexPos v) (harea : area v = 1)
    {y : ℝ} (hy : 0 ≤ y) :
    let K := sidesOf v hm hv harea
    Tendsto (fun n : ℕ => (Measure.pi fun _ : Fin n => polygonSample v hm hv harea)
      {x | ∃ j, x j ∈ cornerOverlap K (y / n)}) atTop (𝓝 0) := by
  intro K
  exact PoissonPP.iid_hit_limit_zero (fun _ => polygonSample v hm hv harea)
    (fun n : ℕ => cornerOverlap K (y / n)) (fun _ => measurableSet_cornerOverlap K _)
    (cornerOverlap_scaled_mass_zero hm hv harea hy)

end Enclosing
