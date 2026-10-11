import LeanProofs.AcuteTetra.Cone

/-!
# Acute tetrahedron: the uniform measure on the unit sphere, and Archimedes' theorem

`unif` is the uniform probability measure on the unit sphere `S² ⊂ ℝ³`, realised on `ℝ³` as the
radial projection of normalised volume on the unit ball. (`unif_eq_toSphere` identifies it with
Mathlib's `volume.toSphere`, normalised.) It is invariant under every linear isometry, and for a
unit vector `u` the height `⟪x, u⟫` is uniform on `[-1, 1]` (Archimedes' hat-box theorem):

* `unif_le`: `unif {x | ⟪x, u⟫ ≤ t} = (1 + t)/2` for `-1 ≤ t ≤ 1`;
* `unif_eq_zero`: `unif {x | ⟪x, u⟫ = t} = 0`;
* `unif_lt`: `unif {x | ⟪x, u⟫ < t} = (1 + t)/2` for `-1 ≤ t ≤ 1`.
-/

namespace AcuteTetra

open MeasureTheory Real Set Metric

/-- Radial projection onto the unit sphere (`0 ↦ 0`). -/
noncomputable def nrm (y : E3) : E3 := ‖y‖⁻¹ • y

lemma nrm_meas : Measurable nrm := measurable_id.norm.inv.smul measurable_id

/-- The uniform probability measure on the unit sphere of `ℝ³`. -/
noncomputable def unif : Measure E3 :=
  (volume (ball (0 : E3) 1))⁻¹ • (volume.restrict (ball (0 : E3) 1)).map nrm

lemma vol_ball : volume (ball (0 : E3) 1) = ENNReal.ofReal (4 * π / 3) := by
  rw [EuclideanSpace.volume_ball_fin_three]; simp; ring_nf

lemma vol_ball_ne_zero : volume (ball (0 : E3) 1) ≠ 0 := by
  rw [vol_ball]; simp; positivity

lemma vol_ball_ne_top : volume (ball (0 : E3) 1) ≠ ⊤ := by rw [vol_ball]; simp

lemma unif_apply {S : Set E3} (hS : MeasurableSet S) :
    unif S = (volume (ball (0 : E3) 1))⁻¹ * volume (ball 0 1 ∩ nrm ⁻¹' S) := by
  rw [unif, Measure.smul_apply, Measure.map_apply nrm_meas hS, Measure.restrict_apply (nrm_meas hS),
    inter_comm, smul_eq_mul]

instance : IsProbabilityMeasure unif := by
  constructor
  rw [unif_apply MeasurableSet.univ, preimage_univ, inter_univ,
    ENNReal.inv_mul_cancel vol_ball_ne_zero vol_ball_ne_top]

lemma nrm_map (L : E3 ≃ₗᵢ[ℝ] E3) (y : E3) : L (nrm y) = nrm (L y) := by
  simp [nrm, L.norm_map]

/-- `unif` is invariant under every linear isometry. -/
theorem unif_map (L : E3 ≃ₗᵢ[ℝ] E3) : unif.map L = unif := by
  ext S hS
  rw [Measure.map_apply L.continuous.measurable hS, unif_apply hS,
    unif_apply (L.continuous.measurable hS)]
  congr 1
  have : ball (0 : E3) 1 ∩ nrm ⁻¹' (L ⁻¹' S) = L ⁻¹' (ball 0 1 ∩ nrm ⁻¹' S) := by
    ext y
    simp [nrm_map]
  rw [this, (L.measurePreserving).measure_preimage
    (measurableSet_ball.inter (nrm_meas hS)).nullMeasurableSet]

lemma unif_preimage (L : E3 ≃ₗᵢ[ℝ] E3) {S : Set E3} (hS : MeasurableSet S) :
    unif (L ⁻¹' S) = unif S := by
  rw [← Measure.map_apply L.continuous.measurable hS, unif_map]

/-- `unif` lives on the unit sphere. -/
theorem unif_ae_norm : ∀ᵐ x ∂unif, ‖x‖ = 1 := by
  have hS : MeasurableSet {a : E3 | ¬‖a‖ = 1} :=
    (measurableSet_eq_fun measurable_norm measurable_const).compl
  rw [ae_iff, unif_apply hS]
  refine mul_eq_zero_of_right _ (measure_mono_null (t := {0}) ?_ (measure_singleton 0))
  intro y ⟨hy, hn⟩
  simp only [mem_preimage, mem_ofPred_eq, nrm, norm_smul, norm_inv, norm_norm] at hn
  by_contra h0
  exact hn (inv_mul_cancel₀ (norm_ne_zero_iff.2 h0))

lemma vol_congr_off_zero {A B : Set E3} (h : ∀ y, y ≠ 0 → (y ∈ A ↔ y ∈ B)) :
    volume A = volume B := by
  refine measure_congr ?_
  filter_upwards [Measure.ae_ne volume (0 : E3)] with y hy
  exact propext (h y hy)

/-- The first coordinate vector. -/
noncomputable def e0 : E3 := EuclideanSpace.single 0 1

lemma inner_e0 (x : E3) : inner ℝ x e0 = x 0 := by
  simp [e0, EuclideanSpace.inner_single_right]

/-- Archimedes for the axis `e0` and `0 ≤ t ≤ 1` (closed or open cap). -/
lemma unif_cap_e0 (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (strict : Bool) :
    unif {x | if strict then t < inner ℝ x e0 else t ≤ inner ℝ x e0} =
      ENNReal.ofReal ((1 - t) / 2) := by
  have hmeas : MeasurableSet {x : E3 | if strict then t < inner ℝ x e0 else t ≤ inner ℝ x e0} := by
    have hc : Continuous fun x : E3 => inner ℝ x e0 := by fun_prop
    cases strict
    · exact measurableSet_le measurable_const hc.measurable
    · exact measurableSet_lt measurable_const hc.measurable
  rw [unif_apply hmeas]
  have hcone : volume (ball (0 : E3) 1 ∩ nrm ⁻¹' {x | if strict then t < inner ℝ x e0
      else t ≤ inner ℝ x e0}) = volume (cone t strict) := by
    refine vol_congr_off_zero fun y hy => ?_
    have hn : 0 < ‖y‖ := norm_pos_iff.2 hy
    simp only [cone, mem_inter_iff, mem_ball_zero_iff, mem_preimage, mem_ofPred_eq, inner_e0, nrm,
      PiLp.smul_apply, smul_eq_mul]
    refine and_congr_right fun _ => ?_
    cases strict
    · simp only [Bool.false_eq_true, ite_false]
      rw [← div_eq_inv_mul, le_div_iff₀ hn, mul_comm]
    · simp only [ite_true]
      rw [← div_eq_inv_mul, lt_div_iff₀ hn, mul_comm]
  rw [hcone, vol_cone t ht0 ht1 strict, vol_ball, ← ENNReal.ofReal_inv_of_pos (by positivity),
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  field_simp
  ring

/-- A linear isometry taking a unit vector `u` to `e0`. -/
noncomputable def toE0 (u : E3) : E3 ≃ₗᵢ[ℝ] E3 := (ℝ ∙ (u - e0))ᗮ.reflection

lemma inner_toE0 (u : E3) (hu : ‖u‖ = 1) (x : E3) : inner ℝ x u = inner ℝ (toE0 u x) e0 := by
  have h : toE0 u u = e0 := by
    rw [toE0, Submodule.reflection_sub]
    simp [e0, hu]
  rw [← h, LinearIsometryEquiv.inner_map_map]

/-- Archimedes for any unit axis `u` and `0 ≤ t ≤ 1`. -/
lemma unif_cap (u : E3) (hu : ‖u‖ = 1) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (strict : Bool) :
    unif {x | if strict then t < inner ℝ x u else t ≤ inner ℝ x u} =
      ENNReal.ofReal ((1 - t) / 2) := by
  have hmeas : MeasurableSet {x : E3 | if strict then t < inner ℝ x e0 else t ≤ inner ℝ x e0} := by
    have hc : Continuous fun x : E3 => inner ℝ x e0 := by fun_prop
    cases strict
    · exact measurableSet_le measurable_const hc.measurable
    · exact measurableSet_lt measurable_const hc.measurable
  have : {x : E3 | if strict then t < inner ℝ x u else t ≤ inner ℝ x u} =
      toE0 u ⁻¹' {x | if strict then t < inner ℝ x e0 else t ≤ inner ℝ x e0} := by
    ext x; simp [inner_toE0 u hu x]
  rw [this, unif_preimage _ hmeas, unif_cap_e0 t ht0 ht1 strict]

lemma meas_inner_le (u : E3) (t : ℝ) : MeasurableSet {x : E3 | inner ℝ x u ≤ t} :=
  measurableSet_le (by fun_prop) measurable_const

lemma meas_inner_lt (u : E3) (t : ℝ) : MeasurableSet {x : E3 | inner ℝ x u < t} :=
  measurableSet_lt (by fun_prop) measurable_const

lemma meas_inner_eq (u : E3) (t : ℝ) : MeasurableSet {x : E3 | inner ℝ x u = t} :=
  measurableSet_eq_fun (by fun_prop) measurable_const

lemma neg_set_lt (u : E3) (t : ℝ) :
    {x : E3 | inner ℝ x u < t} = {x | if true then -t < inner ℝ x (-u) else -t ≤ inner ℝ x (-u)} := by
  ext x; simp [inner_neg_right]

lemma neg_set_le (u : E3) (t : ℝ) :
    {x : E3 | inner ℝ x u ≤ t} = {x | if false then -t < inner ℝ x (-u) else -t ≤ inner ℝ x (-u)} := by
  ext x; simp [inner_neg_right]

/-- **Archimedes.** The open lower cap. -/
theorem unif_lt (u : E3) (hu : ‖u‖ = 1) (t : ℝ) (ht0 : -1 ≤ t) (ht1 : t ≤ 1) :
    unif {x | inner ℝ x u < t} = ENNReal.ofReal ((1 + t) / 2) := by
  have hu' : ‖-u‖ = 1 := by rw [norm_neg, hu]
  rcases le_total t 0 with h | h
  · rw [neg_set_lt, unif_cap (-u) hu' (-t) (by linarith) (by linarith)]
    ring_nf
  · have hc : {x : E3 | inner ℝ x u < t} = {x | if false then t < inner ℝ x u
        else t ≤ inner ℝ x u}ᶜ := by
      ext x; simp
    rw [hc, prob_compl_eq_one_sub (by simpa using (measurableSet_le measurable_const
      (by fun_prop : Measurable fun x : E3 => inner ℝ x u))), unif_cap u hu t h ht1 false,
      ← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ (by linarith)]
    ring_nf

/-- **Archimedes.** The closed lower cap. -/
theorem unif_le (u : E3) (hu : ‖u‖ = 1) (t : ℝ) (ht0 : -1 ≤ t) (ht1 : t ≤ 1) :
    unif {x | inner ℝ x u ≤ t} = ENNReal.ofReal ((1 + t) / 2) := by
  have hu' : ‖-u‖ = 1 := by rw [norm_neg, hu]
  rcases le_total t 0 with h | h
  · rw [neg_set_le, unif_cap (-u) hu' (-t) (by linarith) (by linarith)]
    ring_nf
  · have hc : {x : E3 | inner ℝ x u ≤ t} = {x | if true then t < inner ℝ x u
        else t ≤ inner ℝ x u}ᶜ := by
      ext x; simp
    rw [hc, prob_compl_eq_one_sub (by simpa using (measurableSet_lt measurable_const
      (by fun_prop : Measurable fun x : E3 => inner ℝ x u))), unif_cap u hu t h ht1 true,
      ← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ (by linarith)]
    ring_nf

/-- Level sets of a height are null. -/
theorem unif_eq_zero (u : E3) (hu : ‖u‖ = 1) (t : ℝ) : unif {x | inner ℝ x u = t} = 0 := by
  rcases lt_or_ge t (-1) with h | h
  · refine measure_mono_null (fun x hx => ?_) ((unif_lt u hu (-1) le_rfl (by norm_num)).trans
      (by norm_num))
    simp only [mem_ofPred_eq] at hx ⊢; linarith
  rcases le_or_gt t 1 with h' | h'
  · have hsub : {x : E3 | inner ℝ x u = t} = {x | inner ℝ x u ≤ t} \ {x | inner ℝ x u < t} := by
      ext x; simp only [mem_ofPred_eq, mem_sdiff, not_lt]
      constructor
      · intro hx; exact ⟨hx.le, hx.ge⟩
      · intro hx; exact le_antisymm hx.1 hx.2
    rw [hsub, measure_sdiff (fun x hx => by simp only [mem_ofPred_eq] at hx ⊢; exact hx.le)
      (meas_inner_lt u t).nullMeasurableSet (measure_ne_top _ _), unif_le u hu t h h',
      unif_lt u hu t h h', tsub_self]
  · refine measure_mono_null (fun x hx => ?_)
      ((unif_cap u hu 1 zero_le_one le_rfl false).trans (by norm_num))
    simp only [mem_ofPred_eq, Bool.false_eq_true, ite_false] at hx ⊢; linarith

/-- Level sets of `⟪x, v⟫` are null for any `v ≠ 0`. -/
theorem unif_eq_zero' (v : E3) (hv : v ≠ 0) (t : ℝ) : unif {x | inner ℝ x v = t} = 0 := by
  have hn : 0 < ‖v‖ := norm_pos_iff.2 hv
  have hu : ‖‖v‖⁻¹ • v‖ = 1 := by rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne']
  have : {x : E3 | inner ℝ x v = t} = {x | inner ℝ x (‖v‖⁻¹ • v) = ‖v‖⁻¹ * t} := by
    ext x
    simp only [mem_ofPred_eq, real_inner_smul_right]
    constructor
    · intro h; rw [h]
    · intro h; exact mul_left_cancel₀ (inv_ne_zero hn.ne') h
  rw [this, unif_eq_zero _ hu]

open scoped Pointwise in
/-- `unif` is Mathlib's surface measure `volume.toSphere` on the unit sphere, normalised to total
mass `1`: the definition used here is the standard uniform distribution on `S²`. -/
theorem unif_eq_toSphere :
    unif = ((volume : Measure E3).toSphere univ)⁻¹ •
      ((volume : Measure E3).toSphere).map ((↑) : sphere (0 : E3) 1 → E3) := by
  ext S hS
  rw [Measure.smul_apply, Measure.map_apply measurable_subtype_coe hS, smul_eq_mul,
    Measure.toSphere_apply' _ (measurable_subtype_coe hS), Measure.toSphere_apply_univ,
    unif_apply hS, Subtype.image_preimage_coe, finrank_euclideanSpace_fin]
  have h3 : ((3 : ℕ) : ENNReal) ≠ 0 := by norm_num
  have h3' : ((3 : ℕ) : ENNReal) ≠ ⊤ := by norm_num
  rw [ENNReal.mul_inv (Or.inl h3) (Or.inl h3')]
  set V := volume (ball (0 : E3) 1)
  set W := volume (Ioo (0 : ℝ) 1 • (sphere (0 : E3) 1 ∩ S))
  rw [show ((3 : ℕ) : ENNReal)⁻¹ * V⁻¹ * (((3 : ℕ) : ENNReal) * W) =
      (((3 : ℕ) : ENNReal)⁻¹ * ((3 : ℕ) : ENNReal)) * (V⁻¹ * W) by ring,
    ENNReal.inv_mul_cancel h3 h3', one_mul]
  congr 1
  refine vol_congr_off_zero fun y hy => ?_
  have hn : 0 < ‖y‖ := norm_pos_iff.2 hy
  simp only [mem_inter_iff, mem_ball_zero_iff, mem_preimage, Set.mem_smul, mem_Ioo,
    mem_sphere_zero_iff_norm]
  constructor
  · rintro ⟨hy1, hS'⟩
    refine ⟨‖y‖, ⟨hn, hy1⟩, nrm y, ⟨?_, hS'⟩, ?_⟩
    · rw [nrm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne']
    · rw [nrm, smul_smul, mul_inv_cancel₀ hn.ne', one_smul]
  · rintro ⟨r, ⟨hr0, hr1⟩, x, ⟨hx, hxS⟩, rfl⟩
    have hrx : ‖r • x‖ = r := by rw [norm_smul, hx, mul_one, Real.norm_of_nonneg hr0.le]
    refine ⟨by rw [hrx]; exact hr1, ?_⟩
    rw [nrm, hrx, smul_smul, inv_mul_cancel₀ hr0.ne', one_smul]
    exact hxS

end AcuteTetra
