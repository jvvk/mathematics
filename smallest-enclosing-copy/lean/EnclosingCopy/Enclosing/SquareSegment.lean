import EnclosingCopy.Enclosing.SegmentCount
import EnclosingCopy.Enclosing.SquareModel

/-!
# The square in the Poisson model: the segment candidates

The square has two pairs of parallel sides, so four ordered pairs `(k, k + 2)`. For each,
`seg_candidate_limit` gives the limit `segDensity · ∫ chordWeightInf` of the probability of a
segment candidate. For the square:

* `segDensity_square`: `∫∫∫_{s₀ < -s₂ < s₁} (s₁ - s₀) = ∫∫_{s₀ < s₁} (s₁ - s₀)² = 1/12`
  (the paper's `σ_k w_k`, with `w_k = 1`);
* `chordInf_square`: at scale `ε`, tilt `θ` and normal translation `w`, the copy fits for chord
  positions `|c| ≤ ρ` when `|w| ≤ ρ`, `ρ = (-ε - |θ|)/2`, and `S = 1`, so the chord weight
  integrates to `∫∫ e^{-2t} ((t - |θ|) + (t - |θ|)²) = 1/4 + 1/4 = 1/2`
  (the paper's width and area terms);
* `square_seg_candidate_limit`: each ordered pair contributes `1/24`;
* `square_candidates_limit`: the certified vertex candidate (`1/12`) and the four segment
  candidates (`4 · 1/24`) have probabilities summing, in the limit, to `1/4 = p₄`.
-/

namespace Enclosing

open MeasureTheory Set Real ENNReal

/-! ### The side pairs -/

lemma squarePair (k : Fin 4) : ParPair squareSides k (k + 2) := by
  fin_cases k <;> refine ⟨?_, ?_, ?_, ?_⟩ <;>
    first
    | (simp [squareSides]; done)
    | (simp [squareSides]; norm_num; done)
    | skip
  · exact ⟨1, by simp [squareSides, dot, tang]⟩
  · exact ⟨2, by simp [squareSides, dot, tang]⟩
  · exact ⟨3, by simp [squareSides, dot, tang]⟩
  · exact ⟨0, by simp [squareSides, dot, tang]⟩

lemma slopeSum_square (k : Fin 4) : slopeSum squareSides k = 1 := by
  unfold slopeSum positiveSides
  rw [Finset.sum_filter]
  fin_cases k <;> simp [Fin.sum_univ_four, squareSides, dot, tang] <;> norm_num

/-! ### The position density -/

/-- `∫⁻` of a continuous function, nonnegative on `[p, q]`, is the interval integral. -/
lemma lintegral_Icc_ofReal {g : ℝ → ℝ} (hg : Continuous g) {p q : ℝ} (hpq : p ≤ q)
    (hnn : ∀ x ∈ Icc p q, 0 ≤ g x) :
    ∫⁻ x, ENNReal.ofReal (g x) ∂(volume.restrict (Icc p q)) =
      ENNReal.ofReal (∫ x in p..q, g x) := by
  rw [← ofReal_integral_eq_lintegral_ofReal (hg.integrableOn_Icc)
    ((ae_restrict_iff' measurableSet_Icc).2 (Filter.Eventually.of_forall hnn)),
    integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le hpq]

/-- `∫_{-1/2}^{1/2} max(x - a, 0)² dx = (1/2 - a)³/3` for `a ∈ [-1/2, 1/2]`. -/
lemma integral_max_sq {a : ℝ} (ha : a ∈ Icc (-1 / 2 : ℝ) (1 / 2)) :
    ∫ x in (-1 / 2 : ℝ)..(1 / 2), (max (x - a) 0) ^ 2 = (1 / 2 - a) ^ 3 / 3 := by
  have hc : Continuous fun x : ℝ => (max (x - a) 0) ^ 2 := by fun_prop
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := a)
    (hc.intervalIntegrable _ _) (hc.intervalIntegrable _ _)]
  have h1 : ∫ x in (-1 / 2 : ℝ)..a, (max (x - a) 0) ^ 2 = 0 := by
    rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ))]
    · simp
    · intro x hx
      rw [uIcc_of_le ha.1] at hx
      simp [max_eq_right (by linarith [hx.2] : x - a ≤ 0)]
  have h2 : ∫ x in a..(1 / 2), (max (x - a) 0) ^ 2 = ∫ x in a..(1 / 2), (x - a) ^ 2 := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le ha.2] at hx
    simp only [max_eq_left (by linarith [hx.1] : 0 ≤ x - a)]
  rw [h1, h2, intervalIntegral.integral_comp_sub_right (fun x => x ^ 2), integral_pow]
  ring

/-- The position density of the square, for any ordered pair: `1/12`. -/
theorem segDensity_square (k kb : Fin 4) : segDensity squareSides k kb = ENNReal.ofReal (1 / 12) := by
  set ν : Measure ℝ := volume.restrict (Icc (-1 / 2 : ℝ) (1 / 2))
  let G : ℝ × ℝ × ℝ → ℝ≥0∞ := {p : ℝ × ℝ × ℝ | p.1 < -p.2.2 ∧ -p.2.2 < p.2.1}.indicator
    (fun p => ENNReal.ofReal (p.2.1 - p.1))
  have hGm : Measurable G := by
    refine (ENNReal.measurable_ofReal.comp (by fun_prop)).indicator ?_
    exact (measurableSet_lt (f := fun p : ℝ × ℝ × ℝ => p.1) (g := fun p => -p.2.2)
      (by fun_prop) (by fun_prop)).inter
      (measurableSet_lt (f := fun p : ℝ × ℝ × ℝ => -p.2.2) (g := fun p => p.2.1)
        (by fun_prop) (by fun_prop))
  have hmp : MeasurePreserving (fun s : Fin 3 → ℝ => (s 0, s 1, s 2))
      (Measure.pi fun _ => ν) (ν.prod (ν.prod ν)) := by
    have h := ((MeasurePreserving.id ν).prod (measurePreserving_finTwoArrow ν)).comp
      (measurePreserving_piFinSuccAbove (fun _ : Fin 3 => ν) 0)
    convert h using 1
    funext s
    rfl
  have hint : segDensity squareSides k kb =
      ∫⁻ s : Fin 3 → ℝ, G (s 0, s 1, s 2) ∂(Measure.pi fun _ => ν) := by
    unfold segDensity segRow
    have hm : (Measure.pi fun r : Fin 3 => volume.restrict
        (Icc (squareSides.a (![k, k, kb] r)) (squareSides.b (![k, k, kb] r)))) =
          Measure.pi fun _ => ν := by
      simp [squareSides, ν]
    rw [hm]
    apply lintegral_congr
    intro s
    simp only [G, squareSides, Set.indicator, mem_ofPred_eq]
    norm_num
  rw [hint, hmp.lintegral_comp hGm, lintegral_prod _ hGm.aemeasurable]
  -- the innermost integral, over `s₂`
  have hin : ∀ s₀ ∈ Icc (-1 / 2 : ℝ) (1 / 2), ∀ s₁ ∈ Icc (-1 / 2 : ℝ) (1 / 2),
      ∫⁻ s₂, G (s₀, s₁, s₂) ∂ν = ENNReal.ofReal ((max (s₁ - s₀) 0) ^ 2) := by
    intro s₀ h₀ s₁ h₁
    have he : (fun s₂ => G (s₀, s₁, s₂)) =
        (Ioo (-s₁) (-s₀)).indicator (fun _ => ENNReal.ofReal (s₁ - s₀)) := by
      funext s₂
      simp only [G, Set.indicator, mem_ofPred_eq, mem_Ioo]
      congr 1
      apply propext
      constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
    rw [he, lintegral_indicator_const measurableSet_Ioo,
      Measure.restrict_apply measurableSet_Ioo,
      inter_eq_left.mpr (Ioo_subset_Icc_self.trans (Icc_subset_Icc (by linarith [h₁.2])
        (by linarith [h₀.1]))), Real.volume_Ioo]
    rcases le_total 0 (s₁ - s₀) with h | h
    · rw [max_eq_left h, ← ENNReal.ofReal_mul h]; congr 1; ring
    · rw [max_eq_right h, ENNReal.ofReal_of_nonpos h]; simp
  -- the middle integral, over `s₁`
  have hmid : ∀ s₀ ∈ Icc (-1 / 2 : ℝ) (1 / 2),
      ∫⁻ q, G (s₀, q) ∂(ν.prod ν) = ENNReal.ofReal ((1 / 2 - s₀) ^ 3 / 3) := by
    intro s₀ h₀
    rw [lintegral_prod (fun q => G (s₀, q))
      (hGm.comp (measurable_const.prodMk measurable_id)).aemeasurable]
    calc ∫⁻ s₁, ∫⁻ s₂, G (s₀, s₁, s₂) ∂ν ∂ν
        = ∫⁻ s₁, ENNReal.ofReal ((max (s₁ - s₀) 0) ^ 2) ∂ν := by
          apply lintegral_congr_ae
          filter_upwards [ae_restrict_mem measurableSet_Icc] with s₁ h₁
          exact hin s₀ h₀ s₁ h₁
      _ = _ := by
          rw [lintegral_Icc_ofReal (by fun_prop) (by norm_num) (fun _ _ => by positivity),
            integral_max_sq h₀]
  calc ∫⁻ s₀, ∫⁻ q, G (s₀, q) ∂(ν.prod ν) ∂ν
      = ∫⁻ s₀, ENNReal.ofReal ((1 / 2 - s₀) ^ 3 / 3) ∂ν := by
        apply lintegral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Icc] with s₀ h₀
        exact hmid s₀ h₀
    _ = _ := by
        rw [lintegral_Icc_ofReal (by fun_prop) (by norm_num)
          (fun x hx => by have := hx.2; have : 0 ≤ 1 / 2 - x := by linarith
                          positivity)]
        congr 1
        rw [intervalIntegral.integral_div,
          intervalIntegral.integral_comp_sub_left (fun x => x ^ 3), integral_pow]
        norm_num

/-! ### The chord weight -/

lemma segCopy_eq {m : ℕ} (K : Sides m) (k : Fin m) (v : Fin 3 → ℝ) (c : ℝ) :
    segCopy K k v c = (v 0, (v 1 * (K.u k).1 + c * (tang K k).1,
      v 1 * (K.u k).2 + c * (tang K k).2), v 2) := rfl

/-- For the square, the copy fits at chord position `c` iff `|w| ≤ ρ` and `|c| ≤ ρ`, with
`ρ = (-ε - |θ|)/2`. -/
lemma mem_fitChord_square (k : Fin 4) (v : Fin 3 → ℝ) (c : ℝ) :
    c ∈ fitChord squareSides k v ↔
      |v 1| ≤ (-v 0 - |v 2|) / 2 ∧ |c| ≤ (-v 0 - |v 2|) / 2 := by
  change Fits squareSides (segCopy squareSides k v c) ↔ _
  rw [segCopy_eq, fits_iff_region]
  by_cases h : |v 2| ≤ -v 0
  · rw [fittingRegion_square h, mem_prod, mem_Icc, mem_Icc, abs_le, abs_le]
    fin_cases k <;> simp [squareSides, tang] <;> constructor <;> intro hh <;>
      obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hh <;> refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith
  · rw [fittingRegion_square_empty (lt_of_not_ge h)]
    simp only [mem_empty_iff_false, false_iff, not_and]
    intro h1
    have := abs_nonneg (v 1)
    linarith

lemma chordWeightInf_square (k : Fin 4) (v : Fin 3 → ℝ) :
    chordWeightInf squareSides k v =
      {v : Fin 3 → ℝ | |v 1| ≤ (-v 0 - |v 2|) / 2}.indicator
        (fun v => ENNReal.ofReal (Real.exp (2 * v 0) * (1 + (-v 0 - |v 2|)))) v := by
  unfold chordWeightInf
  rw [slopeSum_square]
  by_cases h : |v 1| ≤ (-v 0 - |v 2|) / 2
  · have hI : fitChord squareSides k v = Icc (-((-v 0 - |v 2|) / 2)) ((-v 0 - |v 2|) / 2) := by
      ext c; rw [mem_fitChord_square, mem_Icc, ← abs_le]; simp [h]
    have hρ : 0 ≤ (-v 0 - |v 2|) / 2 := (abs_nonneg _).trans h
    rw [indicator_of_mem (show v ∈ {v | (fitChord squareSides k v).Nonempty} by
        rw [mem_ofPred_eq, hI]; exact nonempty_Icc.mpr (by linarith)),
      indicator_of_mem (show v ∈ {v : Fin 3 → ℝ | |v 1| ≤ (-v 0 - |v 2|) / 2} from h), hI,
      Real.volume_Icc, Pi.one_apply, ENNReal.ofReal_one, one_mul,
      show (-v 0 - |v 2|) / 2 - -((-v 0 - |v 2|) / 2) = -v 0 - |v 2| by ring,
      ← ENNReal.ofReal_one, ← ENNReal.ofReal_add zero_le_one (by linarith),
      ← ENNReal.ofReal_mul (Real.exp_pos _).le]
  · have hE : fitChord squareSides k v = ∅ := by
      ext c; rw [mem_fitChord_square]; simp [h]
    rw [indicator_of_notMem (show v ∉ {v | (fitChord squareSides k v).Nonempty} by
        rw [mem_ofPred_eq, hE]; simp),
      indicator_of_notMem (show v ∉ {v : Fin 3 → ℝ | |v 1| ≤ (-v 0 - |v 2|) / 2} from h), hE,
      measure_empty]
    simp

/-- `∫_{u > 0} u e^{-2u} du = 1/4`, as a lower integral. -/
lemma lintegral_lin_exp :
    ∫⁻ u in Ioi (0 : ℝ), ENNReal.ofReal (u * Real.exp (-(2 * u))) = ENNReal.ofReal (1 / 4) := by
  have hg : IntegrableOn (fun u : ℝ => u ^ (1 : ℝ) * Real.exp (-2 * u ^ (1 : ℝ))) (Ioi 0) :=
    integrableOn_rpow_mul_exp_neg_mul_rpow (by norm_num) (by norm_num) (by norm_num)
  have hint : IntegrableOn (fun u : ℝ => u * Real.exp (-(2 * u))) (Ioi 0) := by
    refine hg.congr_fun (fun u _ => ?_) measurableSet_Ioi
    simp only [Real.rpow_one, neg_mul]
  have h1 := integral_pow_mul_exp_neg 1 (by norm_num : (0 : ℝ) < 2)
  simp only [pow_one] at h1
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    ((ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun u hu => by
      have : (0 : ℝ) < u := hu; positivity)), h1]
  norm_num [Nat.factorial]

/-- `∫_{t > c} e^{-2t} (t - c) dt = e^{-2c}/4`, as a lower integral. -/
lemma lintegral_inner_lin (c : ℝ) :
    ∫⁻ t in Ioi c, ENNReal.ofReal (Real.exp (-2 * t) * (t - c))
      = ENNReal.ofReal (Real.exp (-(2 * c))) * ENNReal.ofReal (1 / 4) := by
  rw [← lintegral_lin_exp, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    ← lintegral_indicator measurableSet_Ioi, ← lintegral_indicator measurableSet_Ioi,
    ← lintegral_add_right_eq_self _ c]
  refine lintegral_congr fun u => ?_
  by_cases hu : 0 < u
  · rw [indicator_of_mem (show u + c ∈ Ioi c by simp [hu]),
      indicator_of_mem (show u ∈ Ioi 0 from hu), ← ENNReal.ofReal_mul (Real.exp_pos _).le]
    congr 1
    rw [show -2 * (u + c) = -(2 * c) + -(2 * u) by ring, Real.exp_add]
    ring
  · rw [indicator_of_notMem (show u + c ∉ Ioi c by simpa using hu),
      indicator_of_notMem (show u ∉ Ioi (0 : ℝ) from hu)]

/-- Width plus area: `∫_{t > c} e^{-2t} ((t - c) + (t - c)²) dt = e^{-2c}/2`. -/
lemma lintegral_inner_seg (c : ℝ) :
    ∫⁻ t in Ioi c, ENNReal.ofReal (Real.exp (-2 * t) * ((t - c) + (t - c) ^ 2))
      = ENNReal.ofReal (Real.exp (-(2 * c))) * ENNReal.ofReal (1 / 2) := by
  have hsplit : ∀ t ∈ Ioi c, ENNReal.ofReal (Real.exp (-2 * t) * ((t - c) + (t - c) ^ 2)) =
      ENNReal.ofReal (Real.exp (-2 * t) * (t - c)) +
        ENNReal.ofReal (Real.exp (-2 * t) * (t - c) ^ 2) := by
    intro t ht
    have : 0 ≤ t - c := by have : c < t := ht; linarith
    rw [← ENNReal.ofReal_add (by positivity) (by positivity), mul_add]
  rw [setLIntegral_congr_fun measurableSet_Ioi hsplit,
    lintegral_add_left (by fun_prop), lintegral_inner_lin, lintegral_inner_square, ← mul_add,
    ← ENNReal.ofReal_add (by norm_num) (by norm_num)]
  norm_num

/-- The chord weight of the square integrates to `1/2`: the width term `1/4` plus the area
term `1/4`. -/
theorem chordInf_square (k : Fin 4) :
    ∫⁻ v, chordWeightInf squareSides k v = ENNReal.ofReal (1 / 2) := by
  let H : ℝ × ℝ × ℝ → ℝ≥0∞ := {p : ℝ × ℝ × ℝ | |p.2.2| ≤ (-p.2.1 - |p.1|) / 2}.indicator
    (fun p => ENNReal.ofReal (Real.exp (2 * p.2.1) * (1 + (-p.2.1 - |p.1|))))
  have hHm : Measurable H := by
    refine (ENNReal.measurable_ofReal.comp (by fun_prop)).indicator ?_
    exact measurableSet_le (f := fun p : ℝ × ℝ × ℝ => |p.2.2|)
      (g := fun p => (-p.2.1 - |p.1|) / 2) (by fun_prop) (by fun_prop)
  have hmp : MeasurePreserving (fun v : Fin 3 → ℝ => (v 2, v 0, v 1))
      (Measure.pi fun _ => (volume : Measure ℝ))
      ((volume : Measure ℝ).prod ((volume : Measure ℝ).prod volume)) := by
    have h := ((MeasurePreserving.id (volume : Measure ℝ)).prod
      (measurePreserving_finTwoArrow (volume : Measure ℝ))).comp
      (measurePreserving_piFinSuccAbove (fun _ : Fin 3 => (volume : Measure ℝ)) 2)
    convert h using 1
    funext v
    rfl
  have hv : (∫⁻ v, chordWeightInf squareSides k v) =
      ∫⁻ v : Fin 3 → ℝ, H (v 2, v 0, v 1) ∂(Measure.pi fun _ => (volume : Measure ℝ)) := by
    rw [← volume_pi]
    apply lintegral_congr
    intro v
    rw [chordWeightInf_square]
    rfl
  rw [hv, hmp.lintegral_comp hHm, lintegral_prod _ hHm.aemeasurable]
  -- the integral over the normal translation `w`
  have hw : ∀ θ ε : ℝ, ∫⁻ w, H (θ, ε, w) =
      ENNReal.ofReal (Real.exp (2 * ε) * (1 + (-ε - |θ|))) * ENNReal.ofReal (-ε - |θ|) := by
    intro θ ε
    have he : (fun w => H (θ, ε, w)) = (Icc (-((-ε - |θ|) / 2)) ((-ε - |θ|) / 2)).indicator
        (fun _ => ENNReal.ofReal (Real.exp (2 * ε) * (1 + (-ε - |θ|)))) := by
      funext w
      simp only [H, Set.indicator, mem_ofPred_eq, mem_Icc, ← abs_le]
    rw [he, lintegral_indicator_const measurableSet_Icc, Real.volume_Icc]
    congr 2
    ring
  -- the integral over the scale `ε = -t`
  have hε : ∀ θ : ℝ, ∫⁻ q, H (θ, q) ∂((volume : Measure ℝ).prod volume) =
      ENNReal.ofReal (Real.exp (-(2 * |θ|))) * ENNReal.ofReal (1 / 2) := by
    intro θ
    rw [lintegral_prod (fun q => H (θ, q))
      (hHm.comp (measurable_const.prodMk measurable_id)).aemeasurable]
    simp_rw [hw θ]
    have hneg := (Measure.measurePreserving_neg (volume : Measure ℝ)).lintegral_comp_emb
      (Homeomorph.neg ℝ).measurableEmbedding
      (fun ε : ℝ => ENNReal.ofReal (Real.exp (2 * ε) * (1 + (-ε - |θ|))) *
        ENNReal.ofReal (-ε - |θ|))
    rw [← hneg, ← lintegral_inner_seg, ← lintegral_indicator measurableSet_Ioi]
    apply lintegral_congr
    intro t
    simp only [neg_neg]
    by_cases ht : |θ| < t
    · rw [indicator_of_mem (show t ∈ Ioi |θ| from ht),
        ← ENNReal.ofReal_mul (by have := Real.exp_pos (2 * -t); positivity)]
      congr 1
      ring_nf
    · rw [indicator_of_notMem (show t ∉ Ioi |θ| from ht),
        ENNReal.ofReal_of_nonpos (by linarith : t - |θ| ≤ 0), mul_zero]
  simp_rw [hε]
  rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top,
    ← ofReal_integral_eq_lintegral_ofReal integrable_exp_neg_two_abs
      (Filter.Eventually.of_forall fun θ => (Real.exp_pos _).le)]
  have := integral_exp_neg_abs (c := 2) (by norm_num)
  rw [this, ← ENNReal.ofReal_mul (by norm_num)]
  norm_num

/-! ### The limits -/

/-- **Each ordered pair of parallel sides of the square contributes `1/24`**: the probability
of a segment candidate on the pair `(k, k + 2)`, in the model truncated at depth `n`. -/
theorem square_seg_candidate_limit (k : Fin 4) :
    Filter.Tendsto (fun n : ℕ => PoissonPP.law (Λ squareSides n)
      {ω | HasSegCand squareSides k (k + 2) n ω}) Filter.atTop
      (nhds (ENNReal.ofReal (1 / 24))) := by
  have h := seg_candidate_limit (squarePair k)
  rw [segDensity_square, chordInf_square, ← ENNReal.ofReal_mul (by norm_num)] at h
  convert h using 3
  norm_num

/-- **`p₄ = 1/4` as a sum of candidate probabilities.** The probability of a certified vertex
candidate tends to `1/12` and that of a segment candidate on each of the four ordered pairs of
parallel sides to `1/24`; the five limits sum to `1/4`. (That these events are almost surely
disjoint and exhaust the event `E` is the classification step, `square_optFit_prob`.) -/
theorem square_candidates_limit :
    Filter.Tendsto (fun n : ℕ =>
      PoissonPP.law (Λ squareSides n) {ω | HasVertexCandidate squareSides n ω} +
        ∑ k : Fin 4, PoissonPP.law (Λ squareSides n) {ω | HasSegCand squareSides k (k + 2) n ω})
      Filter.atTop (nhds (ENNReal.ofReal (1 / 4))) := by
  have hv := square_vertex_candidate_limit
  have hs := tendsto_finsetSum (Finset.univ : Finset (Fin 4))
    fun k _ => square_seg_candidate_limit k
  convert hv.add hs using 2
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    show ((4 : ℕ) : ℝ≥0∞) = ENNReal.ofReal 4 by simp, ← ENNReal.ofReal_mul (by norm_num),
    ← ENNReal.ofReal_add (by norm_num) (by norm_num)]
  norm_num

end Enclosing
