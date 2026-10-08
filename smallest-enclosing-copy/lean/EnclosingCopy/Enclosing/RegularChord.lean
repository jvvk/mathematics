import EnclosingCopy.Enclosing.RegularSegment

/-!
# Theorem 8 for the regular `q`-gon: the chord weight

The chord weight of a pair of parallel sides `(k, k̄)` is
`e^{2ε} (1{chord ≠ ∅} + S |chord|)`, integrated over the scale `ε`, the normal translation `w`
and the tilt `θ`. For any polygon, the chord lengths integrate over `w` to the area of the fitting
region (`lintegral_fitChord`: the map `(w, y) ↦ w u + y t` has determinant one). For the regular
`q`-gon with the parallel pair, the chord at `w` is nonempty iff `|w| ≤ ρ`, `ρ = r t - c|θ|`
(`fitChord_nonempty_reg`), and the area is `q tan (π/q) ρ²`, so (`chordInf_reg`)

  `∫ chordWeightInf = ∫∫ e^{-2t} (2ρ + S q tan(π/q) ρ²) = (r/c) (r/2 + S q tan(π/q) r²/4)`.
-/

namespace Enclosing

open MeasureTheory Set Real ENNReal

/-- Slices along a unit direction integrate to the area. -/
lemma lintegral_slices {u : ℝ × ℝ} (hu : u.1 ^ 2 + u.2 ^ 2 = 1) {F : Set (ℝ × ℝ)}
    (hF : MeasurableSet F) :
    ∫⁻ w : ℝ, volume {y : ℝ | (w * u.1 + y * -u.2, w * u.2 + y * u.1) ∈ F} = volume F := by
  let Φ : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ) :=
    Matrix.toLin (Module.Basis.finTwoProd ℝ) (Module.Basis.finTwoProd ℝ) !![u.1, -u.2; u.2, u.1]
  have hΦ : ∀ p : ℝ × ℝ, Φ p = (u.1 * p.1 + -u.2 * p.2, u.2 * p.1 + u.1 * p.2) :=
    fun p => Matrix.toLin_finTwoProd_apply _ _ _ _ p
  have hdet : LinearMap.det Φ = 1 := by
    rw [LinearMap.det_toLin, Matrix.det_fin_two_of]; linarith
  have hpre : volume (Φ ⁻¹' F) = volume F := by
    rw [Measure.addHaar_preimage_linearMap _ (by rw [hdet]; norm_num), hdet]
    simp
  have hm : MeasurableSet (Φ ⁻¹' F) :=
    hF.preimage (LinearMap.continuous_of_finiteDimensional Φ).measurable
  rw [← hpre, Measure.volume_eq_prod, Measure.prod_apply hm]
  refine lintegral_congr fun w => ?_
  congr 1
  ext y
  simp only [mem_preimage, mem_ofPred_eq, hΦ]
  constructor <;> intro h <;> convert h using 2 <;> ring

variable {m : ℕ} (K : Sides m) (k : Fin m)

lemma fitChord_eq (v : Fin 3 → ℝ) :
    fitChord K k v = {y | (v 1 * (K.u k).1 + y * -(K.u k).2, v 1 * (K.u k).2 + y * (K.u k).1) ∈
      fittingRegion K (-v 0) (v 2)} := by
  ext y
  change Fits K (segCopy K k v y) ↔ _
  rw [segCopy_eq, fits_iff_region]
  simp [tang]

/-- **The chord lengths integrate to the area of the fitting region.** -/
lemma lintegral_fitChord (hu : (K.u k).1 ^ 2 + (K.u k).2 ^ 2 = 1) (ε θ : ℝ) :
    ∫⁻ w, volume (fitChord K k ![ε, w, θ]) = volume (fittingRegion K (-ε) θ) := by
  have he : ∀ w, fitChord K k ![ε, w, θ] = {y | (w * (K.u k).1 + y * -(K.u k).2,
      w * (K.u k).2 + y * (K.u k).1) ∈ fittingRegion K (-ε) θ} := fun w => by
    rw [fitChord_eq]; rfl
  simp_rw [he]
  exact lintegral_slices hu (measurableSet_fittingRegion K _ _)

lemma measurable_chordWeightInf : Measurable (chordWeightInf K k) :=
  measurable_of_tendsto_metrizable (fun n => measurable_chordWeight (K := K) (k := k) (n : ℝ))
    (tendsto_pi_nhds.2 fun v => tendsto_chordWeight (K := K) (k := k) v)

section Reg

variable {q : ℕ} {K : Sides q} {r c : ℝ} (hK : IsReg K r c)
include hK

omit hK in
lemma dot_un_le (a b : Fin q) : |dot (un q a) (un q b)| ≤ 1 := by
  simp only [dot, un]
  rw [← cos_sub]
  exact abs_cos_le_one _

/-- For the regular `q`-gon, the chord at normal translation `w` is nonempty iff `|w| ≤ ρ`. -/
lemma fitChord_nonempty_reg (hc : 0 ≤ c) {k kb : Fin q} (hP : ParPair K k kb) (v : Fin 3 → ℝ) :
    (fitChord K k v).Nonempty ↔ |v 1| ≤ r * -v 0 - c * |v 2| := by
  rw [fitChord_eq, fitReg_eq hK hc]
  have hu := hP.unit
  have hpar := hP.par
  constructor
  · rintro ⟨y, hy⟩
    have h1 := hy k
    have h2 := hy kb
    rw [← hK.u] at h1 h2
    rw [hpar] at h2
    simp only [dot, Prod.fst_neg, Prod.snd_neg] at h1 h2
    rw [abs_le]
    constructor <;> nlinarith [hu]
  · intro h
    refine ⟨0, fun j => ?_⟩
    have hd := dot_un_le (q := q) k j
    rw [← hK.u k] at hd
    have e : dot (v 1 * (K.u k).1 + 0 * -(K.u k).2, v 1 * (K.u k).2 + 0 * (K.u k).1) (un q j) =
        v 1 * dot (K.u k) (un q j) := by simp only [dot]; ring
    rw [e]
    calc v 1 * dot (K.u k) (un q j) ≤ |v 1 * dot (K.u k) (un q j)| := le_abs_self _
      _ = |v 1| * |dot (K.u k) (un q j)| := abs_mul _ _
      _ ≤ |v 1| * 1 := mul_le_mul_of_nonneg_left hd (abs_nonneg _)
      _ ≤ _ := by rw [mul_one]; exact h

/-- The integral over the normal translation `w`: `e^{2ε} (2ρ + S · area)`. -/
lemma lintegral_w_reg (hc : 0 ≤ c) {k kb : Fin q} (hP : ParPair K k kb) (ε θ : ℝ) :
    ∫⁻ w, chordWeightInf K k ![ε, w, θ] =
      ENNReal.ofReal (exp (2 * ε)) * (ENNReal.ofReal (2 * (r * -ε - c * |θ|)) +
        ENNReal.ofReal (slopeSum K k) * volume (fittingRegion K (-ε) θ)) := by
  unfold chordWeightInf
  simp only [Matrix.cons_val_zero]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  congr 1
  set ρ := r * -ε - c * |θ|
  have hind : ∀ w, {v : Fin 3 → ℝ | (fitChord K k v).Nonempty}.indicator 1 ![ε, w, θ] =
      (Icc (-ρ) ρ).indicator (1 : ℝ → ℝ≥0∞) w := by
    intro w
    have hiff := fitChord_nonempty_reg hK hc hP ![ε, w, θ]
    simp only [Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons] at hiff
    by_cases h : |w| ≤ ρ
    · rw [indicator_of_mem (show ![ε, w, θ] ∈ {v : Fin 3 → ℝ | (fitChord K k v).Nonempty} from
        hiff.2 h), indicator_of_mem (show w ∈ Icc (-ρ) ρ from abs_le.1 h)]
      rfl
    · rw [indicator_of_notMem (show ![ε, w, θ] ∉ {v : Fin 3 → ℝ | (fitChord K k v).Nonempty} from
        fun h' => h (hiff.1 h')), indicator_of_notMem (show w ∉ Icc (-ρ) ρ from
          fun h' => h (abs_le.2 h'))]
  simp_rw [hind]
  rw [lintegral_add_left (measurable_one.indicator measurableSet_Icc),
    lintegral_indicator_one measurableSet_Icc, Real.volume_Icc,
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_fitChord K k hP.unit]
  congr 2
  ring

/-- **The chord weight of a pair of parallel sides of the regular `q`-gon integrates to
`(r/c)(r/2 + S q tan(π/q) r²/4)`.** -/
theorem chordInf_reg [NeZero q] (hq : 3 ≤ q) (hr : 0 < r) (hc : 0 < c) {k kb : Fin q}
    (hP : ParPair K k kb) (hS : 0 ≤ slopeSum K k) :
    ∫⁻ v, chordWeightInf K k v = ENNReal.ofReal ((r / c) *
      (r / 2 + slopeSum K k * (q * tan (π / q)) * r ^ 2 / 4)) := by
  have hT : 0 ≤ q * tan (π / q) := by
    have := tanq_pos hq; have := q_pos hq; positivity
  set S := slopeSum K k
  let H : ℝ × ℝ × ℝ → ℝ≥0∞ := fun p => chordWeightInf K k ![p.2.1, p.2.2, p.1]
  have hHm : Measurable H := by
    refine (measurable_chordWeightInf K k).comp (measurable_pi_iff.2 fun i => ?_)
    fin_cases i <;> simp <;> fun_prop
  have hmp : MeasurePreserving (fun v : Fin 3 → ℝ => (v 2, v 0, v 1))
      (Measure.pi fun _ => (volume : Measure ℝ))
      ((volume : Measure ℝ).prod ((volume : Measure ℝ).prod volume)) := by
    have h := ((MeasurePreserving.id (volume : Measure ℝ)).prod
      (measurePreserving_finTwoArrow (volume : Measure ℝ))).comp
      (measurePreserving_piFinSuccAbove (fun _ : Fin 3 => (volume : Measure ℝ)) 2)
    convert h using 1
    funext v
    rfl
  have hv : (∫⁻ v, chordWeightInf K k v) =
      ∫⁻ v : Fin 3 → ℝ, H (v 2, v 0, v 1) ∂(Measure.pi fun _ => (volume : Measure ℝ)) := by
    rw [← volume_pi]
    refine lintegral_congr fun v => ?_
    simp only [H]
    congr 1
    funext i
    fin_cases i <;> rfl
  rw [hv, hmp.lintegral_comp hHm, lintegral_prod _ hHm.aemeasurable]
  -- the scale integral, for each tilt
  have hε : ∀ θ : ℝ, ∫⁻ p, H (θ, p) ∂((volume : Measure ℝ).prod volume) =
      ENNReal.ofReal (exp (-((2 * c / r) * |θ|))) *
        ENNReal.ofReal (r / 2 + S * (q * tan (π / q)) * r ^ 2 / 4) := by
    intro θ
    rw [lintegral_prod (fun p => H (θ, p))
      (hHm.comp (measurable_const.prodMk measurable_id)).aemeasurable]
    simp only [H]
    simp_rw [lintegral_w_reg hK hc.le hP]
    have hneg := (Measure.measurePreserving_neg (volume : Measure ℝ)).lintegral_comp_emb
      (Homeomorph.neg ℝ).measurableEmbedding
      (fun ε : ℝ => ENNReal.ofReal (exp (2 * ε)) * (ENNReal.ofReal (2 * (r * -ε - c * |θ|)) +
        ENNReal.ofReal S * volume (fittingRegion K (-ε) θ)))
    rw [← hneg]
    simp only [neg_neg]
    set a := c * |θ| / r
    have ha : 0 ≤ a := by positivity
    have hra : ∀ t, r * t - c * |θ| = r * (t - a) := fun t => by
      simp only [a]; field_simp
    calc ∫⁻ t, ENNReal.ofReal (exp (2 * -t)) * (ENNReal.ofReal (2 * (r * t - c * |θ|)) +
          ENNReal.ofReal S * volume (fittingRegion K t θ))
        = ∫⁻ t, (Ioi a).indicator (fun t => ENNReal.ofReal (2 * r) *
            ENNReal.ofReal (exp (-2 * t) * (t - a)) + ENNReal.ofReal (S * (q * tan (π / q)) * r ^ 2) *
            ENNReal.ofReal (exp (-2 * t) * (t - a) ^ 2)) t := by
          refine lintegral_congr_ae ?_
          filter_upwards [Measure.ae_ne volume a] with t ht
          have hρ : r * t - c * |θ| ≠ 0 := by
            rw [hra]; exact mul_ne_zero hr.ne' (sub_ne_zero.2 ht)
          have hvol := volume_polyReg hK hq hc hρ
          rw [← fitReg_eq hK hc.le, hra] at hvol
          rw [hvol, hra]
          by_cases h : a < t
          · rw [indicator_of_mem (show t ∈ Ioi a from h), max_eq_left (by nlinarith)]
            have h0 : 0 ≤ t - a := by linarith
            rw [← ENNReal.ofReal_mul hS, ← ENNReal.ofReal_add (by positivity) (by positivity),
              ← ENNReal.ofReal_mul (exp_pos _).le, ← ENNReal.ofReal_mul (by positivity),
              ← ENNReal.ofReal_mul (by positivity),
              ← ENNReal.ofReal_add (by positivity) (by positivity)]
            congr 1
            rw [show -2 * t = 2 * -t by ring]
            ring
          · rw [indicator_of_notMem (show t ∉ Ioi a from h),
              max_eq_right (by nlinarith [not_lt.1 h]),
              ENNReal.ofReal_of_nonpos (by nlinarith [not_lt.1 h] : 2 * (r * (t - a)) ≤ 0)]
            simp
      _ = _ := by
          rw [lintegral_indicator measurableSet_Ioi, lintegral_add_left (by fun_prop),
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_inner_lin,
            lintegral_inner_square,
            show -(2 * a) = -((2 * c / r) * |θ|) by simp only [a]; ring]
          rw [← mul_assoc, ← mul_assoc, mul_comm (ENNReal.ofReal (2 * r)),
            mul_comm (ENNReal.ofReal (S * (q * tan (π / q)) * r ^ 2)), mul_assoc, mul_assoc,
            ← mul_add, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
            ← ENNReal.ofReal_add (by positivity) (by positivity)]
          congr 2
          ring
  simp_rw [hε]
  rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top, lintegral_exp_neg_abs (by positivity),
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  field_simp

end Reg

end Enclosing
