import LeanProofs.AcuteTetra.Sphere

/-!
# Acute tetrahedron: one cap calculation (Section 6 of the paper)

For independent uniform `a, b`, the dot product `⟪a, b⟫` is uniform on `[-1, 1]` (`law_inner`).
Given `a, b`, a third uniform point `c` makes `a + b + c` short with probability
`q = (2 - s)/4`, `s = ‖a + b‖ = √(2 + 2⟪a, b⟫)` (`q_eq`). Averaging,

* `alpha_eq`: `α = E q = 1/6` (one face sum short);
* `gamma_eq`: `γ = E q² = 1/24` (two face sums sharing two vertices both short).
-/

namespace AcuteTetra

open MeasureTheory Real Set Metric

/-- **Archimedes, as a law.** For a unit vector `b`, `⟪a, b⟫` is uniform on `[-1, 1]`. -/
theorem law_inner (b : E3) (hb : ‖b‖ = 1) :
    unif.map (fun a => inner ℝ a b) = ENNReal.ofReal (1 / 2) • volume.restrict (Icc (-1 : ℝ) 1) := by
  have hm : Measurable fun a : E3 => inner ℝ a b := by fun_prop
  refine Measure.ext_of_Iic _ _ fun t => ?_
  rw [Measure.map_apply hm measurableSet_Iic, Measure.smul_apply, Measure.restrict_apply
    measurableSet_Iic, smul_eq_mul]
  have hpre : (fun a : E3 => inner ℝ a b) ⁻¹' Iic t = {a | inner ℝ a b ≤ t} := rfl
  rw [hpre]
  rcases lt_or_ge t (-1) with h | h
  · have h0 : Iic t ∩ Icc (-1 : ℝ) 1 = ∅ := by
      ext x; simp only [mem_inter_iff, mem_Iic, mem_Icc, mem_empty_iff_false, iff_false]
      intro hx; linarith [hx.1, hx.2.1]
    rw [h0, measure_empty, mul_zero]
    refine measure_mono_null (fun x hx => ?_) ((unif_lt b hb (-1) le_rfl (by norm_num)).trans
      (by norm_num))
    simp only [mem_ofPred_eq] at hx ⊢; linarith
  rcases le_or_gt t 1 with h' | h'
  · have h0 : Iic t ∩ Icc (-1 : ℝ) 1 = Icc (-1) t := by
      ext x; simp only [mem_inter_iff, mem_Iic, mem_Icc]
      constructor
      · intro hx; exact ⟨hx.2.1, hx.1⟩
      · intro hx; exact ⟨hx.2, hx.1, by linarith [hx.2]⟩
    rw [h0, Real.volume_Icc, unif_le b hb t h h', ← ENNReal.ofReal_mul (by norm_num)]
    congr 1; ring
  · have h0 : Iic t ∩ Icc (-1 : ℝ) 1 = Icc (-1) 1 := by
      ext x; simp only [mem_inter_iff, mem_Iic, mem_Icc]
      constructor
      · intro hx; exact hx.2
      · intro hx; exact ⟨by linarith [hx.2], hx⟩
    rw [h0, Real.volume_Icc, ← ENNReal.ofReal_mul (by norm_num)]
    have h1 : unif {a | inner ℝ a b ≤ t} = 1 := by
      refine le_antisymm prob_le_one ?_
      calc (1 : ENNReal) = unif {a | inner ℝ a b ≤ 1} := by
            rw [unif_le b hb 1 (by norm_num) le_rfl]; norm_num
        _ ≤ _ := measure_mono fun x hx => by simp only [mem_ofPred_eq] at hx ⊢; linarith
    rw [h1]; norm_num

lemma lintegral_inner (b : E3) (hb : ‖b‖ = 1) (g : ℝ → ENNReal) (hg : Measurable g) :
    ∫⁻ a, g (inner ℝ a b) ∂unif = ENNReal.ofReal (1 / 2) * ∫⁻ t in Icc (-1 : ℝ) 1, g t := by
  rw [← lintegral_map hg (by fun_prop), law_inner b hb, lintegral_smul_measure, smul_eq_mul]

/-- The cap probability: `c` makes `a + b + c` short. -/
noncomputable def q (a b : E3) : ENNReal := unif {c | ‖a + b + c‖ < 1}

/-- The cap probability as a function of `t = ⟪a, b⟫`. -/
noncomputable def qf (t : ℝ) : ℝ := (2 - √(2 + 2 * t)) / 4

lemma q_eq (a b : E3) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hab : inner ℝ a b ≠ -1) :
    q a b = ENNReal.ofReal (qf (inner ℝ a b)) := by
  set s := ‖a + b‖ with hs
  have hs2 : s ^ 2 = 2 + 2 * inner ℝ a b := by
    rw [hs, norm_add_sq_real, ha, hb]; ring
  have hab' : -1 ≤ inner ℝ a b := by
    have := abs_real_inner_le_norm a b; rw [ha, hb] at this; linarith [neg_abs_le (inner ℝ a b)]
  have hab'' : inner ℝ a b ≤ 1 := by
    have := real_inner_le_norm a b; rw [ha, hb] at this; linarith
  have hspos : 0 < s := by
    have : 0 < s ^ 2 := by rw [hs2]; have := lt_of_le_of_ne hab' (Ne.symm hab); linarith
    rcases (norm_nonneg (a + b)).lt_or_eq with h | h
    · exact h
    · rw [hs, ← h] at this; norm_num at this
  have hsq : s = √(2 + 2 * inner ℝ a b) := by rw [← hs2, Real.sqrt_sq hspos.le]
  have hs2le : s ≤ 2 := by
    have : s ^ 2 ≤ 4 := by rw [hs2]; linarith
    nlinarith
  set u := s⁻¹ • (a + b) with hu
  have hu1 : ‖u‖ = 1 := by rw [hu, norm_smul, norm_inv, norm_norm, ← hs, inv_mul_cancel₀ hspos.ne']
  have hset : {c : E3 | ‖a + b + c‖ < 1} =ᵐ[unif] {c | inner ℝ c u < -s / 2} := by
    filter_upwards [unif_ae_norm] with c hc
    refine propext ?_
    change ‖a + b + c‖ < 1 ↔ inner ℝ c u < -s / 2
    have h1 : ‖a + b + c‖ ^ 2 = s ^ 2 + 2 * (s * inner ℝ c u) + 1 := by
      rw [norm_add_sq_real, hc, hu, real_inner_smul_right, ← hs, real_inner_comm]
      field_simp
    constructor
    · intro h
      have : ‖a + b + c‖ ^ 2 < 1 := by nlinarith [norm_nonneg (a + b + c)]
      nlinarith
    · intro h
      have : ‖a + b + c‖ ^ 2 < 1 := by nlinarith
      nlinarith [norm_nonneg (a + b + c)]
  rw [q, measure_congr hset, unif_lt u hu1 (-s / 2) (by linarith) (by linarith), qf, ← hsq]
  congr 1; ring

lemma qf_nonneg (t : ℝ) (ht : t ≤ 1) : 0 ≤ qf t := by
  unfold qf
  have : √(2 + 2 * t) ≤ 2 := by
    rw [Real.sqrt_le_left (by norm_num)]; linarith
  linarith

lemma qf_cont : Continuous qf := by unfold qf; fun_prop

/-- `∫_{-1}^{1} √(2 + 2t) dt = 8/3`. -/
lemma integral_sqrt_lin : ∫ t in (-1 : ℝ)..1, √(2 + 2 * t) = 8 / 3 := by
  have hF : ∀ t ∈ Ioo (-1 : ℝ) 1,
      HasDerivAt (fun t => (2 + 2 * t) * √(2 + 2 * t) / 3) (√(2 + 2 * t)) t := by
    intro t ht
    have hpos : 0 < 2 + 2 * t := by linarith [ht.1]
    have h1 : HasDerivAt (fun t : ℝ => 2 + 2 * t) 2 t := by
      simpa using ((hasDerivAt_id t).const_mul 2).const_add 2
    have h2 := h1.sqrt hpos.ne'
    have := (h1.mul h2).div_const 3
    convert this using 1
    have hs := Real.sq_sqrt hpos.le
    have hsp := Real.sqrt_pos.2 hpos
    set r := √(2 + 2 * t)
    rw [← hs]
    field_simp
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (by norm_num)
    (by fun_prop) hF ((by fun_prop : Continuous fun t : ℝ => √(2 + 2 * t)).intervalIntegrable _ _)]
  have : √(4 : ℝ) = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  norm_num [this]

lemma integral_qf : ∫ t in (-1 : ℝ)..1, qf t = 1 / 3 := by
  unfold qf
  rw [intervalIntegral.integral_div, intervalIntegral.integral_sub intervalIntegrable_const
    ((by fun_prop : Continuous fun t : ℝ => √(2 + 2 * t)).intervalIntegrable _ _),
    integral_sqrt_lin, intervalIntegral.integral_const]
  norm_num

lemma integral_qf_sq : ∫ t in (-1 : ℝ)..1, qf t ^ 2 = 1 / 12 := by
  have h : ∫ t in (-1 : ℝ)..1, qf t ^ 2 =
      ∫ t in (-1 : ℝ)..1, ((6 + 2 * t) - 4 * √(2 + 2 * t)) / 16 := by
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [uIcc_of_le (by norm_num)] at ht
    have := Real.sq_sqrt (by linarith [ht.1] : (0 : ℝ) ≤ 2 + 2 * t)
    simp only [qf]
    nlinarith
  rw [h, intervalIntegral.integral_div, intervalIntegral.integral_sub
    ((by fun_prop : Continuous fun t : ℝ => 6 + 2 * t).intervalIntegrable _ _)
    ((by fun_prop : Continuous fun t : ℝ => 4 * √(2 + 2 * t)).intervalIntegrable _ _),
    intervalIntegral.integral_const_mul, integral_sqrt_lin, intervalIntegral.integral_add
    intervalIntegrable_const ((by fun_prop : Continuous fun t : ℝ => 2 * t).intervalIntegrable _ _),
    intervalIntegral.integral_const_mul, integral_id, intervalIntegral.integral_const]
  norm_num

lemma lintegral_Icc_ofReal (h : ℝ → ℝ) (hc : Continuous h) (hn : ∀ t ∈ Icc (-1 : ℝ) 1, 0 ≤ h t) :
    ∫⁻ t in Icc (-1 : ℝ) 1, ENNReal.ofReal (h t) = ENNReal.ofReal (∫ t in (-1 : ℝ)..1, h t) := by
  rw [← ofReal_integral_eq_lintegral_ofReal hc.integrableOn_Icc
    (ae_restrict_of_forall_mem measurableSet_Icc hn), integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num)]

lemma q_meas : Measurable fun p : E3 × E3 => q p.1 p.2 := by
  have hS : MeasurableSet {x : E3 × (E3 × E3) | ‖x.2.1 + x.2.2 + x.1‖ < 1} :=
    measurableSet_lt (by fun_prop) measurable_const
  exact measurable_measure_prodMk_right (μ := unif) hS

/-- Off a null set, `q a b = qf ⟪a, b⟫` for a fixed unit `b`. -/
lemma q_ae (b : E3) (hb : ‖b‖ = 1) :
    ∀ᵐ a ∂unif, q a b = ENNReal.ofReal (qf (inner ℝ a b)) := by
  have hnull : ∀ᵐ a ∂unif, inner ℝ a b ≠ -1 := by
    rw [ae_iff]; simpa using unif_eq_zero b hb (-1)
  filter_upwards [unif_ae_norm, hnull] with a ha hab
  exact q_eq a b ha hb hab

/-- Moments of `q` over an independent pair reduce to one integral over `[-1, 1]`. -/
lemma lintegral_q_pow (n : ℕ) :
    ∫⁻ p, q p.1 p.2 ^ n ∂(unif.prod unif) =
      ENNReal.ofReal (1 / 2) * ENNReal.ofReal (∫ t in (-1 : ℝ)..1, qf t ^ n) := by
  rw [lintegral_prod_symm _ (q_meas.pow_const n).aemeasurable]
  have hb : ∀ᵐ b ∂unif, ∫⁻ a, q a b ^ n ∂unif =
      ENNReal.ofReal (1 / 2) * ENNReal.ofReal (∫ t in (-1 : ℝ)..1, qf t ^ n) := by
    filter_upwards [unif_ae_norm] with b hb
    rw [lintegral_congr_ae ((q_ae b hb).mono fun a ha => by rw [ha]),
      lintegral_inner b hb (fun t => ENNReal.ofReal (qf t) ^ n)
        ((ENNReal.measurable_ofReal.comp qf_cont.measurable).pow_const n)]
    congr 1
    rw [setLIntegral_congr_fun measurableSet_Icc
      (fun t ht => (ENNReal.ofReal_pow (qf_nonneg t ht.2) n).symm)]
    exact lintegral_Icc_ofReal _ (qf_cont.pow n) fun t ht => pow_nonneg (qf_nonneg t ht.2) n
  rw [lintegral_congr_ae hb, lintegral_const, measure_univ, mul_one]

/-- `α = 1/6`: the probability that one face sum is short. -/
theorem alpha_eq : ∫⁻ p, q p.1 p.2 ∂(unif.prod unif) = ENNReal.ofReal (1 / 6) := by
  have := lintegral_q_pow 1
  simp only [pow_one] at this
  rw [this, integral_qf, ← ENNReal.ofReal_mul (by norm_num)]
  norm_num

/-- `γ = 1/24`: the probability that two face sums sharing two vertices are both short. -/
theorem gamma_eq : ∫⁻ p, q p.1 p.2 ^ 2 ∂(unif.prod unif) = ENNReal.ofReal (1 / 24) := by
  rw [lintegral_q_pow 2, integral_qf_sq, ← ENNReal.ofReal_mul (by norm_num)]
  norm_num

end AcuteTetra
