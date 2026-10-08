import RandomChords.Corollaries

/-!
# Corollaries 7 and 8: the common hit probability

Scale `b = 1` and put `r = c / b`. The two lines share the probability
`H(r) = Pr{|cos U - (1 + r) cos V| < r}` (`H`, with `(U, V)` uniform on `(0, π)²`; `hit_eq_H` links it
to the configuration of Corollary 5).

* `H_formula` (Corollary 7): `H(r) = (2/π²) ∫₀^{π/2} (arccos [(1+r) cos v - r] - arccos [(1+r) cos v + r]) dv`,
  thresholds clamped to `[-1, 1]`. Given `V = v`, the event asks that `cos U` lie between the two
  thresholds, which has probability (difference of arccosines)/π; reflection `v ↦ π - v` halves the
  range.
* `H_strictMonoOn`, `H_continuousOn`, `H_tendsto_zero`, `H_tendsto_one` (Corollary 7): `H` is
  continuous and strictly increasing on `(0, ∞)`, tends to `0` at `0⁺` and to `1` at `∞`.
* `cor8` (Corollary 8): `H(1) = (2/π²) ∫₀^{π/2} arccos (2 cos v - 1) dv`. (Its numerical value,
  `0.3871287…`, and its agreement with Dan's dilogarithm expression are computed, not formalised.)
-/

open Real MeasureTheory Set Filter Topology
open scoped ENNReal

noncomputable section

namespace Chords

/-- Restrict a threshold to the cosine's range: `[t]_{-1}^{1}`. -/
def clampI (t : ℝ) : ℝ := max (-1) (min 1 t)

lemma clampI_mem (t : ℝ) : clampI t ∈ Icc (-1 : ℝ) 1 :=
  ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩

lemma continuous_clampI : Continuous clampI := by unfold clampI; fun_prop

lemma clampI_neg (t : ℝ) : clampI (-t) = -clampI t := by
  unfold clampI
  rcases le_or_gt t (-1) with h | h
  · rw [min_eq_left (by linarith : (1 : ℝ) ≤ -t), max_eq_right (by norm_num),
      min_eq_right (by linarith : t ≤ 1), max_eq_left h]; norm_num
  rcases le_or_gt t 1 with h' | h'
  · rw [min_eq_right (by linarith : -t ≤ 1), max_eq_right (by linarith : (-1 : ℝ) ≤ -t),
      min_eq_right h', max_eq_right h.le]
  · rw [min_eq_right (by linarith : -t ≤ 1), max_eq_left (by linarith : -t ≤ (-1 : ℝ)),
      min_eq_left h'.le, max_eq_right (by norm_num)]

lemma clampI_mono : Monotone clampI := fun x y h => by
  unfold clampI; exact max_le_max le_rfl (min_le_min le_rfl h)

/-- For `u ∈ (0, π)`: `cos u < c` exactly when `u > arccos [c]`. -/
lemma cos_lt_iff {u : ℝ} (hu : u ∈ Ioo 0 π) (c : ℝ) : cos u < c ↔ arccos (clampI c) < u := by
  obtain ⟨h1, h2⟩ := cos_mem_Ioo hu
  have hcu : cos u ∈ Icc (-1 : ℝ) 1 := ⟨h1.le, h2.le⟩
  have key : cos u < c ↔ cos u < clampI c := by
    unfold clampI
    constructor
    · intro h; exact lt_max_of_lt_right (lt_min h2 h)
    · intro h
      rcases lt_max_iff.1 h with h' | h'
      · linarith
      · exact lt_of_lt_of_le h' (min_le_right _ _)
  rw [key, ← StrictAntiOn.lt_iff_gt Real.strictAntiOn_arccos (clampI_mem c) hcu,
    arccos_cos hu.1.le hu.2.le]

/-- For `u ∈ (0, π)`: `c < cos u` exactly when `u < arccos [c]`. -/
lemma lt_cos_iff {u : ℝ} (hu : u ∈ Ioo 0 π) (c : ℝ) : c < cos u ↔ u < arccos (clampI c) := by
  obtain ⟨h1, h2⟩ := cos_mem_Ioo hu
  have hcu : cos u ∈ Icc (-1 : ℝ) 1 := ⟨h1.le, h2.le⟩
  have key : c < cos u ↔ clampI c < cos u := by
    unfold clampI
    constructor
    · intro h; exact max_lt h1 (lt_of_le_of_lt (min_le_right _ _) h)
    · intro h
      have := (max_lt_iff.1 h).2
      rcases min_lt_iff.1 this with h' | h'
      · linarith
      · exact h'
  rw [key, ← StrictAntiOn.lt_iff_gt Real.strictAntiOn_arccos hcu (clampI_mem c),
    arccos_cos hu.1.le hu.2.le]

/-- The probability, times `π`, that `cos U` lies between the thresholds for `V = v`. -/
def hitF (r v : ℝ) : ℝ :=
  arccos (clampI ((1 + r) * cos v - r)) - arccos (clampI ((1 + r) * cos v + r))

lemma continuous_hitF : Continuous (fun p : ℝ × ℝ => hitF p.1 p.2) := by
  unfold hitF
  exact (continuous_arccos.comp (continuous_clampI.comp (by fun_prop))).sub
    (continuous_arccos.comp (continuous_clampI.comp (by fun_prop)))

lemma continuous_hitF_r (r : ℝ) : Continuous (hitF r) := by
  unfold hitF
  exact (continuous_arccos.comp (continuous_clampI.comp (by fun_prop))).sub
    (continuous_arccos.comp (continuous_clampI.comp (by fun_prop)))

lemma hitF_nonneg {r : ℝ} (hr : 0 ≤ r) (v : ℝ) : 0 ≤ hitF r v := by
  unfold hitF
  rw [sub_nonneg]
  exact strictAntiOn_arccos.antitoneOn (clampI_mem _) (clampI_mem _)
    (clampI_mono (by linarith))

lemma abs_hitF_le (r v : ℝ) : |hitF r v| ≤ π := by
  unfold hitF
  have := arccos_nonneg (clampI ((1 + r) * cos v - r))
  have := arccos_le_pi (clampI ((1 + r) * cos v - r))
  have := arccos_nonneg (clampI ((1 + r) * cos v + r))
  have := arccos_le_pi (clampI ((1 + r) * cos v + r))
  rw [abs_le]; constructor <;> linarith

lemma hitF_pi_sub (r v : ℝ) : hitF r (π - v) = hitF r v := by
  unfold hitF
  rw [cos_pi_sub, show (1 + r) * -cos v - r = -((1 + r) * cos v + r) by ring,
    show (1 + r) * -cos v + r = -((1 + r) * cos v - r) by ring, clampI_neg, clampI_neg,
    arccos_neg, arccos_neg]
  ring

/-- The event of `H(r)`. -/
def Hset (r : ℝ) : Set (ℝ × ℝ) := {p | |cos p.1 - (1 + r) * cos p.2| < r}

lemma measurableSet_Hset (r : ℝ) : MeasurableSet (Hset r) :=
  measurableSet_lt (Continuous.measurable (by fun_prop)) measurable_const

/-- `H(r) = Pr{|cos U - (1 + r) cos V| < r}`, `(U, V)` uniform on `(0, π)²`. -/
def H (r : ℝ) : ℝ := (volume.restrict sq (Hset r)).toReal / π ^ 2

lemma volume_restrict_sq_ne_top (s : Set (ℝ × ℝ)) : volume.restrict sq s ≠ ∞ :=
  measure_ne_top _ _

/-- The slice of the event at `V = v` is an interval of length `hitF r v`. -/
lemma slice_eq (r v : ℝ) :
    (fun u => (u, v)) ⁻¹' Hset r ∩ Ioo 0 π =
      Ioo (arccos (clampI ((1 + r) * cos v + r))) (arccos (clampI ((1 + r) * cos v - r))) := by
  ext u
  simp only [Hset, mem_inter_iff, mem_preimage, mem_ofPred_eq, mem_Ioo, abs_lt]
  constructor
  · rintro ⟨⟨h1, h2⟩, hu⟩
    exact ⟨(cos_lt_iff hu _).1 (by linarith), (lt_cos_iff hu _).1 (by linarith)⟩
  · rintro ⟨h1, h2⟩
    have hu : u ∈ Ioo 0 π :=
      ⟨lt_of_le_of_lt (arccos_nonneg _) h1, lt_of_lt_of_le h2 (arccos_le_pi _)⟩
    have e1 := (cos_lt_iff hu _).2 h1
    have e2 := (lt_cos_iff hu _).2 h2
    exact ⟨⟨by linarith, by linarith⟩, hu⟩

lemma volume_Hset (r : ℝ) (hr : 0 ≤ r) :
    volume.restrict sq (Hset r) = ENNReal.ofReal (∫ v in (0)..π, hitF r v) := by
  rw [restrict_sq, Measure.prod_apply_symm (measurableSet_Hset r)]
  have hslice : ∀ v, volume.restrict (Ioo 0 π) ((fun u => (u, v)) ⁻¹' Hset r) =
      ENNReal.ofReal (hitF r v) := by
    intro v
    rw [Measure.restrict_apply ((measurableSet_Hset r).preimage (by fun_prop)), slice_eq,
      Real.volume_Ioo]
    rfl
  simp_rw [hslice]
  rw [← ofReal_integral_eq_lintegral_ofReal, intervalIntegral.integral_of_le pi_pos.le,
    integral_Ioc_eq_integral_Ioo]
  · exact (continuous_hitF_r r).integrableOn_Icc
      |>.mono_set Ioo_subset_Icc_self
  · exact Eventually.of_forall (fun v => hitF_nonneg hr v)

lemma integral_hitF_halves (r : ℝ) :
    ∫ v in (0)..π, hitF r v = 2 * ∫ v in (0)..(π / 2), hitF r v := by
  have hc : Continuous (hitF r) := continuous_hitF_r r
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := π / 2)
    (hc.intervalIntegrable _ _) (hc.intervalIntegrable _ _)]
  have h2 : ∫ v in (π / 2)..π, hitF r v = ∫ v in (0)..(π / 2), hitF r v := by
    have := intervalIntegral.integral_comp_sub_left (hitF r) (a := 0) (b := π / 2) π
    rw [show π - π / 2 = π / 2 by ring, sub_zero] at this
    rw [← this]
    exact intervalIntegral.integral_congr (fun v _ => (hitF_pi_sub r v).symm) |>.symm
  rw [h2]; ring

/-- The integral formula of Corollary 7, as a function of `r ≥ 0`. -/
def Hint (r : ℝ) : ℝ := 2 / π ^ 2 * ∫ v in (0)..(π / 2), hitF r v

/-- **Corollary 7, the formula.** -/
theorem H_formula {r : ℝ} (hr : 0 < r) : H r = Hint r := by
  rw [H, volume_Hset r hr.le, ENNReal.toReal_ofReal, integral_hitF_halves, Hint]
  · ring
  · exact intervalIntegral.integral_nonneg pi_pos.le (fun v _ => hitF_nonneg hr.le v)

lemma continuous_Hint : Continuous Hint := by
  unfold Hint
  exact continuous_const.mul
    (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' continuous_hitF _ _)

lemma Hint_zero : Hint 0 = 0 := by
  unfold Hint hitF; simp

/-- **Corollary 7.** `H` is continuous on `(0, ∞)`. -/
theorem H_continuousOn : ContinuousOn H (Ioi 0) :=
  continuous_Hint.continuousOn.congr (fun _ hr => H_formula hr)

/-- **Corollary 7.** `H(r) → 0` as `r ↓ 0`. -/
theorem H_tendsto_zero : Tendsto H (𝓝[>] 0) (𝓝 0) := by
  have h := continuous_Hint.continuousWithinAt (s := Ioi 0) (x := 0)
  rw [ContinuousWithinAt, Hint_zero] at h
  exact h.congr' (eventually_nhdsWithin_of_forall (fun r hr => (H_formula hr).symm))

/-- **Corollary 7.** `H(r) → 1` as `r → ∞`. -/
theorem H_tendsto_one : Tendsto H atTop (𝓝 1) := by
  have hlim : Tendsto (fun r => ∫ v in (0)..(π / 2), hitF r v) atTop
      (𝓝 (∫ _ in (0)..(π / 2), π)) := by
    refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ => π)
      (Eventually.of_forall fun r =>
        (continuous_hitF_r r).aestronglyMeasurable)
      (Eventually.of_forall fun r => Eventually.of_forall fun v _ => by
        rw [Real.norm_eq_abs]; exact abs_hitF_le r v)
      intervalIntegrable_const ?_
    refine Eventually.of_forall fun v hv => ?_
    rw [uIoc_of_le (by positivity)] at hv
    obtain ⟨hv1, hv2⟩ := hv
    have hc0 : 0 ≤ cos v := cos_nonneg_of_mem_Icc ⟨by linarith [pi_pos], hv2⟩
    have hc1 : cos v < 1 := by
      have := cos_mem_Ioo (t := v) ⟨hv1, by linarith [pi_pos]⟩; exact this.2
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop (max 1 ((1 + cos v) / (1 - cos v)))] with r hr
    have hr1 : 1 ≤ r := le_trans (le_max_left _ _) hr
    have hr2 : (1 + cos v) / (1 - cos v) ≤ r := le_trans (le_max_right _ _) hr
    rw [div_le_iff₀ (by linarith)] at hr2
    unfold hitF
    have e1 : clampI ((1 + r) * cos v + r) = 1 := by
      unfold clampI; rw [min_eq_left (by nlinarith), max_eq_right (by norm_num)]
    have e2 : clampI ((1 + r) * cos v - r) = -1 := by
      unfold clampI; rw [max_eq_left (min_le_of_right_le (by nlinarith))]
    rw [e1, e2, arccos_one, arccos_neg, arccos_one, sub_zero, sub_zero]
  have h := hlim.const_mul (2 / π ^ 2)
  rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero,
    show 2 / π ^ 2 * (π / 2 * π) = 1 by field_simp] at h
  exact h.congr' (eventually_gt_atTop 0 |>.mono fun r hr => (H_formula hr).symm)

/-- `H` is the probability of an increasing family of events. -/
lemma Hset_mono {r r' : ℝ} (hrr : r ≤ r') : Hset r ⊆ Hset r' := by
  intro p hp
  simp only [Hset, mem_ofPred_eq] at hp ⊢
  have hy : |cos p.2| ≤ 1 := abs_cos_le_one _
  have key : cos p.1 - (1 + r') * cos p.2 = (cos p.1 - (1 + r) * cos p.2) - (r' - r) * cos p.2 := by
    ring
  have h1 := abs_sub (cos p.1 - (1 + r) * cos p.2) ((r' - r) * cos p.2)
  rw [abs_mul, abs_of_nonneg (sub_nonneg.2 hrr)] at h1
  have h2 : (r' - r) * |cos p.2| ≤ r' - r := mul_le_of_le_one_right (sub_nonneg.2 hrr) hy
  rw [key]
  linarith

/-- **Corollary 7.** `H` is strictly increasing on `(0, ∞)`: each increase in `r` adds an open
region of the square. -/
theorem H_strictMonoOn : StrictMonoOn H (Ioi 0) := by
  intro r hr r' hr' hrr
  simp only [mem_Ioi] at hr hr'
  -- an open set in `Hset r' \ Hset r`
  set U := {p : ℝ × ℝ | r < |cos p.1 - (1 + r) * cos p.2|} ∩ Hset r' ∩ sq with hU
  have hUo : IsOpen U :=
    ((isOpen_lt continuous_const (by fun_prop)).inter
      (isOpen_lt (by fun_prop) continuous_const)).inter (isOpen_Ioo.prod isOpen_Ioo)
  set y0 := -1 + 1 / (1 + r') with hy0
  set x0 := y0 + (r + r') / 2 * (1 + y0) with hx0
  have hy1 : 1 + y0 = 1 / (1 + r') := by rw [hy0]; ring
  have hy0p : 0 < 1 + y0 := by rw [hy1]; positivity
  have hy0m : y0 ≤ 0 := by
    rw [hy0]; have : 1 / (1 + r') ≤ 1 := by rw [div_le_one (by linarith)]; linarith
    linarith
  have hx0m : x0 < 1 := by
    have h2 : (1 + (r + r') / 2) / (1 + r') < 2 := by rw [div_lt_iff₀ (by linarith)]; linarith
    rw [hx0, show y0 + (r + r') / 2 * (1 + y0) = -1 + (1 + y0) * (1 + (r + r') / 2) by ring, hy1,
      one_div_mul_eq_div]
    linarith
  have hx0p : -1 < x0 := by rw [hx0]; nlinarith
  have hp0 : (arccos x0, arccos y0) ∈ U := by
    have cx : cos (arccos x0) = x0 := cos_arccos hx0p.le hx0m.le
    have cy : cos (arccos y0) = y0 := cos_arccos (by linarith) (by linarith)
    refine ⟨⟨?_, ?_⟩, ⟨arccos_pos.2 hx0m, arccos_lt_pi.2 hx0p⟩,
      ⟨arccos_pos.2 (by linarith), arccos_lt_pi.2 (by linarith)⟩⟩
    · simp only [mem_ofPred_eq, cx, cy]
      rw [lt_abs]; left
      have : x0 - (1 + r) * y0 - r = (r' - r) / 2 * (1 + y0) := by rw [hx0]; ring
      nlinarith
    · simp only [Hset, mem_ofPred_eq, cx, cy, abs_lt]
      constructor
      · have : x0 - (1 + r') * y0 + r' = (r + r') / 2 * (1 + y0) + r' * (1 - y0) := by
          rw [hx0]; ring
        nlinarith
      · have : x0 - (1 + r') * y0 - r' = (r - r') / 2 * (1 + y0) := by rw [hx0]; ring
        nlinarith
  have hUpos : 0 < volume U := hUo.measure_pos volume ⟨_, hp0⟩
  -- measures
  have hsub : Hset r ∩ sq ⊆ Hset r' ∩ sq := inter_subset_inter_left _ (Hset_mono hrr.le)
  have hdisj : Disjoint (Hset r ∩ sq) U := by
    rw [Set.disjoint_left]
    rintro p ⟨hp, -⟩ ⟨⟨hp', -⟩, -⟩
    simp only [Hset, mem_ofPred_eq] at hp hp'
    linarith
  have hUsub : U ⊆ Hset r' ∩ sq := fun p hp => ⟨hp.1.2, hp.2⟩
  have hsqfin : volume sq ≠ ∞ := by
    rw [volume_sq]; exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  have hlt : volume (Hset r ∩ sq) < volume (Hset r' ∩ sq) := by
    calc volume (Hset r ∩ sq) < volume (Hset r ∩ sq) + volume U :=
          ENNReal.lt_add_right (measure_ne_top_of_subset inter_subset_right hsqfin) hUpos.ne'
      _ = volume ((Hset r ∩ sq) ∪ U) := (measure_union hdisj hUo.measurableSet).symm
      _ ≤ volume (Hset r' ∩ sq) := measure_mono (union_subset hsub hUsub)
  unfold H
  rw [Measure.restrict_apply (measurableSet_Hset r), Measure.restrict_apply (measurableSet_Hset r')]
  apply div_lt_div_of_pos_right _ (by positivity)
  exact (ENNReal.toReal_lt_toReal (measure_ne_top_of_subset inter_subset_right hsqfin)
    (measure_ne_top_of_subset inter_subset_right hsqfin)).2 hlt

/-- **Corollary 8.** `H(1) = (2/π²) ∫₀^{π/2} arccos (2 cos v - 1) dv`. -/
theorem cor8 : H 1 = 2 / π ^ 2 * ∫ v in (0)..(π / 2), arccos (2 * cos v - 1) := by
  rw [H_formula one_pos, Hint]
  congr 1
  refine intervalIntegral.integral_congr (fun v hv => ?_)
  rw [uIcc_of_le (by positivity)] at hv
  have hc0 : 0 ≤ cos v := cos_nonneg_of_mem_Icc ⟨by linarith [hv.1, pi_pos], hv.2⟩
  have hc1 : cos v ≤ 1 := cos_le_one v
  unfold hitF clampI
  have e1 : max (-1) (min 1 ((1 + 1) * cos v + 1)) = 1 := by
    rw [min_eq_left (by linarith), max_eq_right (by norm_num)]
  have e2 : max (-1) (min 1 ((1 + 1) * cos v - 1)) = 2 * cos v - 1 := by
    rw [min_eq_right (by linarith), max_eq_right (by linarith)]; ring
  rw [e1, e2, arccos_one, sub_zero]

/-- `H(r)` is the law of Lemma 3 with weights `(1, -(1 + r))`, evaluated below `r`. -/
lemma lawW_Iio (r : ℝ) : lawW (1, -(1 + r)) (Iio r) = volume.restrict sq (Hset r) := by
  rw [lawW, Measure.map_apply (continuous_wsum _).measurable measurableSet_Iio]
  congr 1
  ext p
  simp only [mem_preimage, mem_Iio, wsum, Hset, mem_ofPred_eq]
  rw [show 1 * cos p.1 + -(1 + r) * cos p.2 = cos p.1 - (1 + r) * cos p.2 by ring]

/-- In the configuration of Corollary 5 with `b = 1`, `c = r` (so `a = 1 / r`), both random lines
are at distance less than `r` from the last centre with probability `H(r)`. -/
theorem hit_eq_H {r : ℝ} (hr : 0 < r) (q : ℝ) :
    (volume {ω | dAB (1 / r) 1 (1 / r + 1) q (1 + r) ω < r}).toReal / (4 * π ^ 2) = H r ∧
    (volume {ω | dBC 1 q (1 + r) ω < r}).toReal / (4 * π ^ 2) = H r := by
  have hc := cor5 (a := 1 / r) (b := 1) (by positivity) one_pos hr q
  have hac : 1 / r * r = (1 : ℝ) ^ 2 := by field_simp
  have hlaw := hc.2 hac
  have heq := hc.1.2 hac
  have hBC : volume {ω | dBC 1 q (1 + r) ω < r} = 4 * volume.restrict sq (Hset r) := by
    have := congrArg (fun μ : Measure ℝ => μ (Iio r)) hlaw
    simp only [Measure.smul_apply, smul_eq_mul] at this
    rw [Measure.map_apply (measurable_dBC _ _ _) measurableSet_Iio] at this
    rw [show {ω | dBC 1 q (1 + r) ω < r} = dBC 1 q (1 + r) ⁻¹' Iio r from rfl, this,
      show (1 : ℝ) + r = 1 + r from rfl, lawW_Iio]
  have hAB : volume {ω | dAB (1 / r) 1 (1 / r + 1) q (1 + r) ω < r} =
      volume {ω | dBC 1 q (1 + r) ω < r} := by
    have := congrArg (fun μ : Measure ℝ => μ (Iio r)) heq
    rwa [Measure.map_apply (measurable_dAB _ _ _ _ _) measurableSet_Iio,
      Measure.map_apply (measurable_dBC _ _ _) measurableSet_Iio] at this
  have hfin : volume.restrict sq (Hset r) ≠ ∞ := measure_ne_top _ _
  have key : (volume {ω | dBC 1 q (1 + r) ω < r}).toReal / (4 * π ^ 2) = H r := by
    rw [hBC, ENNReal.toReal_mul, H]
    have : (4 : ℝ≥0∞).toReal = 4 := by norm_num
    rw [this]; field_simp
  exact ⟨by rw [hAB]; exact key, key⟩

end Chords
