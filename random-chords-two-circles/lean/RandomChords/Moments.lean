import RandomChords.Basic
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# Lemma 3: a weighted sum of two arcsine variables determines its weights

`lawW w` is the law of `|w₁ cos U + w₂ cos V|` for `(U, V)` uniform on `(0, π)²`, as a push-forward
of `volume` on the square (mass `π²`). (`cos U` for `U` uniform on `(0, π)` has the arcsine law, the
same as for `U` uniform on `[0, 2π)`.) Lemma 3: `lawW w = lawW w'` exactly when
`{|w₁|, |w₂|} = {|w'₁|, |w'₂|}`. The proof is the paper's: signs and order do not matter by symmetry;
conversely the law determines the upper end `M = |w₁| + |w₂|` of its support and its second moment
`π² (w₁² + w₂²) / 2`, and these two numbers determine `|w₁|, |w₂|` as the roots of
`t² - M t + |w₁ w₂|`.
-/

open Real MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace Chords

/-- `|w₁ cos u + w₂ cos v|`. -/
def wsum (w : ℝ × ℝ) (p : ℝ × ℝ) : ℝ := |w.1 * cos p.1 + w.2 * cos p.2|

lemma continuous_wsum (w : ℝ × ℝ) : Continuous (wsum w) := by unfold wsum; fun_prop

/-- The law of `|w₁ cos U + w₂ cos V|`, `(U, V)` uniform on `(0, π)²` (unnormalised, mass `π²`). -/
def lawW (w : ℝ × ℝ) : Measure ℝ := (volume.restrict sq).map (wsum w)

/-! ### Symmetries -/

lemma mp_reflect1 : MeasurePreserving (fun p : ℝ × ℝ => (π - p.1, p.2))
    (volume.restrict sq) (volume.restrict sq) := by
  have h : MeasurePreserving (fun p : ℝ × ℝ => (π - p.1, p.2)) volume volume := by
    rw [Measure.volume_eq_prod]
    exact (Measure.measurePreserving_sub_left volume π).prod (MeasurePreserving.id volume)
  have h2 := h.restrict_preimage measurableSet_sq
  have hpre : (fun p : ℝ × ℝ => (π - p.1, p.2)) ⁻¹' sq = sq := by
    ext p; simp only [sq, mem_preimage, mem_prod, mem_Ioo]; constructor <;> intro h <;>
      refine ⟨⟨?_, ?_⟩, h.2⟩ <;> linarith [h.1.1, h.1.2]
  rwa [hpre] at h2

lemma mp_reflect2 : MeasurePreserving (fun p : ℝ × ℝ => (p.1, π - p.2))
    (volume.restrict sq) (volume.restrict sq) := by
  have h : MeasurePreserving (fun p : ℝ × ℝ => (p.1, π - p.2)) volume volume := by
    rw [Measure.volume_eq_prod]
    exact (MeasurePreserving.id volume).prod (Measure.measurePreserving_sub_left volume π)
  have h2 := h.restrict_preimage measurableSet_sq
  have hpre : (fun p : ℝ × ℝ => (p.1, π - p.2)) ⁻¹' sq = sq := by
    ext p; simp only [sq, mem_preimage, mem_prod, mem_Ioo]; constructor <;> intro h <;>
      refine ⟨h.1, ?_, ?_⟩ <;> linarith [h.2.1, h.2.2]
  rwa [hpre] at h2

lemma mp_swap : MeasurePreserving Prod.swap (volume.restrict sq) (volume.restrict sq) := by
  have h : MeasurePreserving (Prod.swap : ℝ × ℝ → ℝ × ℝ) volume volume := by
    rw [Measure.volume_eq_prod]; exact Measure.measurePreserving_swap
  have h2 := h.restrict_preimage measurableSet_sq
  have hpre : (Prod.swap : ℝ × ℝ → ℝ × ℝ) ⁻¹' sq = sq := by
    ext p; simp only [sq, mem_preimage, mem_prod, Prod.fst_swap, Prod.snd_swap]; exact and_comm
  rwa [hpre] at h2

lemma lawW_of_comp {w w' : ℝ × ℝ} {f : ℝ × ℝ → ℝ × ℝ}
    (hf : MeasurePreserving f (volume.restrict sq) (volume.restrict sq))
    (h : ∀ p, wsum w' (f p) = wsum w p) : lawW w = lawW w' := by
  rw [lawW, lawW]
  conv_rhs => rw [← hf.map_eq, Measure.map_map (continuous_wsum w').measurable hf.measurable]
  congr 1; funext p; exact (h p).symm

lemma lawW_neg1 (w : ℝ × ℝ) : lawW (-w.1, w.2) = lawW w :=
  (lawW_of_comp mp_reflect1 (fun p => by simp [wsum, cos_pi_sub])).symm

lemma lawW_neg2 (w : ℝ × ℝ) : lawW (w.1, -w.2) = lawW w :=
  (lawW_of_comp mp_reflect2 (fun p => by simp [wsum, cos_pi_sub])).symm

lemma lawW_swap (w : ℝ × ℝ) : lawW (w.2, w.1) = lawW w :=
  (lawW_of_comp mp_swap (fun p => by simp [wsum, add_comm])).symm

lemma lawW_abs (w : ℝ × ℝ) : lawW (|w.1|, |w.2|) = lawW w := by
  have h4 : lawW (-w.1, -w.2) = lawW w := by
    rw [show ((-w.1, -w.2) : ℝ × ℝ) = (-(w.1, -w.2).1, (w.1, -w.2).2) from rfl, lawW_neg1,
      lawW_neg2]
  rcases abs_choice w.1 with h1 | h1 <;> rcases abs_choice w.2 with h2 | h2 <;> rw [h1, h2] <;>
    first | exact lawW_neg2 w | exact lawW_neg1 w | exact h4

/-! ### The upper end of the support -/

lemma wsum_le (w p : ℝ × ℝ) : wsum w p ≤ |w.1| + |w.2| := by
  unfold wsum
  calc |w.1 * cos p.1 + w.2 * cos p.2| ≤ |w.1 * cos p.1| + |w.2 * cos p.2| := abs_add_le _ _
    _ ≤ |w.1| + |w.2| := by
      rw [abs_mul, abs_mul]
      gcongr <;> exact mul_le_of_le_one_right (abs_nonneg _) (abs_cos_le_one _)

lemma lawW_Ioi_eq_zero (w : ℝ × ℝ) {t : ℝ} (ht : |w.1| + |w.2| ≤ t) : lawW w (Ioi t) = 0 := by
  rw [lawW, Measure.map_apply (continuous_wsum w).measurable measurableSet_Ioi]
  have : wsum w ⁻¹' Ioi t = ∅ := by
    ext p; simp only [mem_preimage, mem_Ioi, mem_empty_iff_false, iff_false, not_lt]
    exact (wsum_le w p).trans ht
  rw [this, measure_empty]

lemma lawW_Ioi_pos (w : ℝ × ℝ) {t : ℝ} (ht : t < |w.1| + |w.2|) : 0 < lawW w (Ioi t) := by
  rw [lawW, Measure.map_apply (continuous_wsum w).measurable measurableSet_Ioi,
    Measure.restrict_apply ((continuous_wsum w).measurable measurableSet_Ioi)]
  set M := |w.1| + |w.2| with hMdef
  have hM : 0 ≤ M := by positivity
  -- a point near the corner where both cosines have the signs of the weights
  set m := max (t / M) 0
  have hm1 : m < 1 := by
    rcases eq_or_lt_of_le hM with h | h
    · simp [m, ← h]
    · exact max_lt ((div_lt_one h).2 ht) one_pos
  set δ := arccos ((m + 1) / 2)
  have hδ0 : 0 < δ := arccos_pos.2 (by linarith)
  have hδπ : δ < π := arccos_lt_pi.2 (by linarith [le_max_right (t / M) 0])
  have hcδ : cos δ = (m + 1) / 2 := cos_arccos (by linarith [le_max_right (t / M) 0]) (by linarith)
  set u := if 0 ≤ w.1 then δ else π - δ
  set v := if 0 ≤ w.2 then δ else π - δ
  have hu : w.1 * cos u = |w.1| * cos δ := by
    simp only [u]; split_ifs with h
    · rw [abs_of_nonneg h]
    · rw [cos_pi_sub, abs_of_neg (not_le.1 h)]; ring
  have hv : w.2 * cos v = |w.2| * cos δ := by
    simp only [v]; split_ifs with h
    · rw [abs_of_nonneg h]
    · rw [cos_pi_sub, abs_of_neg (not_le.1 h)]; ring
  have hval : t < wsum w (u, v) := by
    simp only [wsum, hu, hv, ← add_mul, hcδ]
    rcases eq_or_lt_of_le hM with h | h
    · exact lt_of_lt_of_le (by linarith) (abs_nonneg _)
    · have htm : t / M ≤ m := le_max_left _ _
      have h1 : t ≤ M * m := by rwa [div_le_iff₀' h] at htm
      have h2 : M * m < M * ((m + 1) / 2) := mul_lt_mul_of_pos_left (by linarith) h
      rw [abs_of_nonneg (by positivity)]
      linarith [hMdef]
  have hmem : (u, v) ∈ wsum w ⁻¹' Ioi t ∩ sq := by
    refine ⟨hval, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> simp only [u, v] <;> split_ifs <;> linarith
  have hopen : IsOpen (wsum w ⁻¹' Ioi t ∩ sq) :=
    (isOpen_Ioi.preimage (continuous_wsum w)).inter (isOpen_Ioo.prod isOpen_Ioo)
  exact hopen.measure_pos volume ⟨_, hmem⟩

/-- The upper end of the support is a function of the law. -/
lemma sum_abs_eq_of_lawW_eq {w w' : ℝ × ℝ} (h : lawW w = lawW w') :
    |w.1| + |w.2| = |w'.1| + |w'.2| := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · obtain ⟨t, ht1, ht2⟩ := exists_between hlt
    have h0 := lawW_Ioi_eq_zero w ht1.le
    have hp := lawW_Ioi_pos w' ht2
    rw [h] at h0; exact hp.ne' h0
  · obtain ⟨t, ht1, ht2⟩ := exists_between hlt
    have h0 := lawW_Ioi_eq_zero w' ht1.le
    have hp := lawW_Ioi_pos w ht2
    rw [← h] at h0; exact hp.ne' h0

/-! ### The second moment -/

lemma integral_cos_Ioo : ∫ u in Ioo 0 π, cos u = 0 := by
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le pi_pos.le, integral_cos]
  simp

lemma integral_cos_sq_Ioo : ∫ u in Ioo 0 π, cos u ^ 2 = π / 2 := by
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le pi_pos.le, integral_cos_sq]
  simp

lemma integral_one_Ioo : ∫ _ in Ioo 0 π, (1 : ℝ) = π := by
  simp [pi_pos.le]

lemma restrict_sq : volume.restrict sq =
    (volume.restrict (Ioo 0 π)).prod (volume.restrict (Ioo (0 : ℝ) π)) := by
  rw [sq, Measure.volume_eq_prod, Measure.prod_restrict]

instance : IsFiniteMeasure (volume.restrict sq) := by
  rw [restrict_sq]; infer_instance

lemma integrable_sq (f : ℝ × ℝ → ℝ) (hf : Continuous f) (C : ℝ) (hC : ∀ p, |f p| ≤ C) :
    Integrable f (volume.restrict sq) :=
  Integrable.of_bound hf.aestronglyMeasurable C (Filter.Eventually.of_forall hC)

/-- The second moment of the law: `π² (w₁² + w₂²) / 2`. -/
lemma second_moment (w : ℝ × ℝ) :
    ∫ x, x ^ 2 ∂(lawW w) = π ^ 2 * (w.1 ^ 2 + w.2 ^ 2) / 2 := by
  rw [lawW, integral_map (continuous_wsum w).aemeasurable (by fun_prop)]
  have e : ∀ p : ℝ × ℝ, wsum w p ^ 2 =
      w.1 ^ 2 * (cos p.1 ^ 2 * 1) + 2 * w.1 * w.2 * (cos p.1 * cos p.2) + w.2 ^ 2 * (1 * cos p.2 ^ 2) := by
    intro p; rw [wsum, sq_abs]; ring
  simp_rw [e]
  have hb : ∀ p : ℝ × ℝ, |cos p.1 ^ 2 * 1| ≤ 1 := fun p => by
    rw [mul_one, abs_of_nonneg (sq_nonneg _)]; exact cos_sq_le_one _
  have i1 : Integrable (fun p : ℝ × ℝ => cos p.1 ^ 2 * 1) (volume.restrict sq) :=
    integrable_sq _ (by fun_prop) 1 hb
  have i2 : Integrable (fun p : ℝ × ℝ => cos p.1 * cos p.2) (volume.restrict sq) :=
    integrable_sq _ (by fun_prop) 1 (fun p => by
      rw [abs_mul]
      exact (mul_le_mul (abs_cos_le_one _) (abs_cos_le_one _) (abs_nonneg _) zero_le_one).trans
        (by norm_num))
  have i3 : Integrable (fun p : ℝ × ℝ => 1 * cos p.2 ^ 2) (volume.restrict sq) :=
    integrable_sq _ (by fun_prop) 1 (fun p => by
      rw [one_mul, abs_of_nonneg (sq_nonneg _)]; exact cos_sq_le_one _)
  have i12 : Integrable (fun x : ℝ × ℝ => w.1 ^ 2 * (cos x.1 ^ 2 * 1) +
      2 * w.1 * w.2 * (cos x.1 * cos x.2)) (volume.restrict sq) :=
    (i1.const_mul (w.1 ^ 2)).add (i2.const_mul (2 * w.1 * w.2))
  rw [integral_add i12 (i3.const_mul (w.2 ^ 2)),
    integral_add (i1.const_mul (w.1 ^ 2)) (i2.const_mul (2 * w.1 * w.2)), integral_const_mul,
    integral_const_mul, integral_const_mul, restrict_sq,
    integral_prod_mul (fun u => cos u ^ 2) (fun _ => (1 : ℝ)),
    integral_prod_mul (fun u => cos u) (fun v => cos v),
    integral_prod_mul (fun _ => (1 : ℝ)) (fun v => cos v ^ 2),
    integral_cos_sq_Ioo, integral_cos_Ioo, integral_one_Ioo]
  ring

/-! ### Lemma 3 -/

/-- **Lemma 3.** `|w₁ cos U + w₂ cos V|` and `|w'₁ cos U + w'₂ cos V|` have the same law exactly when
`{|w₁|, |w₂|} = {|w'₁|, |w'₂|}`. -/
theorem lemma3 (w w' : ℝ × ℝ) :
    lawW w = lawW w' ↔
      (|w.1| = |w'.1| ∧ |w.2| = |w'.2|) ∨ (|w.1| = |w'.2| ∧ |w.2| = |w'.1|) := by
  constructor
  · intro h
    have hM := sum_abs_eq_of_lawW_eq h
    have h2 := second_moment w
    rw [h, second_moment w'] at h2
    have hq : w.1 ^ 2 + w.2 ^ 2 = w'.1 ^ 2 + w'.2 ^ 2 := by
      have := pi_pos; field_simp at h2; nlinarith [h2, sq_nonneg π]
    rw [← sq_abs w.1, ← sq_abs w.2, ← sq_abs w'.1, ← sq_abs w'.2] at hq
    have hp : |w.1| * |w.2| = |w'.1| * |w'.2| := by
      have := congrArg (fun x => x ^ 2) hM
      linear_combination this / 2 - hq / 2
    have hroot : (|w.1| - |w'.1|) * (|w.1| - |w'.2|) = 0 := by
      linear_combination |w.1| * hM - hp
    rcases mul_eq_zero.1 hroot with h1 | h1
    · left; constructor <;> linarith
    · right; constructor <;> linarith
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · rw [← lawW_abs w, ← lawW_abs w', h1, h2]
    · rw [← lawW_abs w, ← lawW_abs w', h1, h2, ← lawW_swap (|w'.1|, |w'.2|)]

end Chords
