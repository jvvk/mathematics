import EnclosingCopy.Enclosing.GeneralClassify
import EnclosingCopy.Enclosing.TriangleDeriv

/-!
# Triangles in the Poisson model: `P(E_n) → p(K)` of Corollary 2

For side data `K : Sides 3` satisfying `GoodSides`, a triangle has no parallel sides, so by
`general_optFit_limit` the probability of `E` in the truncated model tends to the vertex term
`V · T_nd` (spatial integral times cone density). This file computes the spatial factor;
`TriangleCone` computes the cone density and assembles the limit.

* `fit_integral_triangle`: the map `(ε, C) ↦ (H₁, H₂, H₃)` is linear with determinant `D₃`, and
  `2ε = ∑ Lᵢ Hᵢ`, so `∫ fitWeight = (1/|D₃|) ∫ e^{-Q|Θ|} / (L₁L₂L₃) dΘ = 2 / (|D₃| Q L₁ L₂ L₃)`.
-/

namespace Enclosing
open MeasureTheory Set Matrix ENNReal

variable {K : Sides 3}

/-- Side lengths. -/
def sideL (K : Sides 3) (i : Fin 3) : ℝ := K.b i - K.a i

lemma sideL_pos (i : Fin 3) : 0 < sideL K i := sub_pos.mpr (K.hab i)

/-- `Q = ½ ∑ Lᵢ²`. -/
noncomputable def Qtri (K : Sides 3) : ℝ := (∑ i, sideL K i ^ 2) / 2

lemma Qtri_pos : 0 < Qtri K := by
  unfold Qtri
  have := sideL_pos (K := K) 0
  have : 0 < ∑ i, sideL K i ^ 2 :=
    Finset.sum_pos (fun i _ => by have := sideL_pos (K := K) i; positivity) ⟨0, by simp⟩
  positivity

/-- Identity (1c): `∑ Lᵢ aᵢ = -Q`. -/
lemma sum_L_a : ∑ i, sideL K i * K.a i = -Qtri K := by
  have h := K.sum_sq
  unfold Qtri sideL
  have e : ∀ i, K.b i ^ 2 - K.a i ^ 2 = 2 * ((K.b i - K.a i) * K.a i) + (K.b i - K.a i) ^ 2 :=
    fun i => by ring
  simp_rw [e, Finset.sum_add_distrib, ← Finset.mul_sum] at h
  linarith

/-- `∑ Lᵢ bᵢ = Q`. -/
lemma sum_L_b : ∑ i, sideL K i * K.b i = Qtri K := by
  have h := sum_L_a (K := K)
  have e : ∀ i, sideL K i * K.b i = sideL K i * K.a i + sideL K i ^ 2 :=
    fun i => by unfold sideL; ring
  simp_rw [e, Finset.sum_add_distrib, h]
  unfold Qtri; ring

/-- `2ε = ∑ Lᵢ Hᵢ`. -/
lemma sum_L_Hs (z : Copy) : ∑ i, sideL K i * Hs K z i = 2 * z.1 := by
  have h := sum_line_area K z
  have h1 : ∑ i, z.2.2 * (K.b i ^ 2 - K.a i ^ 2) / 2 = 0 := by
    rw [← Finset.sum_div, ← Finset.mul_sum, K.sum_sq]; simp
  rw [Finset.sum_sub_distrib, h1] at h
  unfold sideL; linarith

/-! ### No two sides of a triangle are parallel -/

lemma tri_cross_ne (hG : GoodSides K) {i j : Fin 3} (hij : i ≠ j) :
    cross (K.u i) (K.u j) ≠ 0 := by
  intro hz
  rcases hG.parallel hz with h | h
  · exact hij h.symm
  -- `u j = -u i`: then the third normal is parallel to `u i`
  obtain ⟨l, hli, hlj⟩ : ∃ l, l ≠ i ∧ l ≠ j := by
    fin_cases i <;> fin_cases j <;>
      first | exact absurd rfl hij | exact ⟨0, by decide, by decide⟩ |
        exact ⟨1, by decide, by decide⟩ | exact ⟨2, by decide, by decide⟩
  have hs1 := K.sum_u1
  have hs2 := K.sum_u2
  have huniv : (Finset.univ : Finset (Fin 3)) = {i, j, l} := by
    apply (Finset.eq_of_subset_of_card_le (Finset.subset_univ _) _).symm
    rw [Finset.card_insert_of_notMem (by simp [hij, hli.symm]), Finset.card_pair hlj.symm]
    simp
  have hsum : ∀ f : Fin 3 → ℝ, ∑ x, f x = f i + f j + f l := by
    intro f
    rw [huniv, Finset.sum_insert (by simp [hij, hli.symm]), Finset.sum_pair hlj.symm]; ring
  rw [hsum] at hs1 hs2
  rw [h] at hs1 hs2
  simp only [Prod.fst_neg, Prod.snd_neg] at hs1 hs2
  have hc : (K.b l - K.a l) * cross (K.u i) (K.u l) = 0 := by
    simp only [cross]; linear_combination (K.u i).1 * hs2 - (K.u i).2 * hs1
  have hc' := (mul_eq_zero.mp hc).resolve_left (sideL_pos (K := K) l).ne'
  rcases hG.parallel hc' with h' | h'
  · exact hli h'
  · exact hlj (hG.inj (h'.trans h.symm))

lemma parPairs_tri (hG : GoodSides K) : parPairs K = ∅ := by
  ext p
  simp only [parPairs, Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty,
    iff_false]
  intro h
  by_cases hp : p.1 = p.2
  · rw [hp] at h
    have hu := hG.unit p.2
    have h1 := congrArg Prod.fst h; have h2 := congrArg Prod.snd h
    simp only [Prod.fst_neg, Prod.snd_neg] at h1 h2
    have e1 : (K.u p.2).1 = 0 := by linarith
    have e2 : (K.u p.2).2 = 0 := by linarith
    rw [e1, e2] at hu; norm_num at hu
  · apply tri_cross_ne hG hp
    rw [h]; simp [cross]; ring

/-! ### The spatial factor -/

variable (K) in
/-- The `3 × 3` determinant of the rows `(hᵢ, uᵢ)`. -/
noncomputable def D3 : ℝ :=
  Matrix.det !![K.h 0, (K.u 0).1, (K.u 0).2; K.h 1, (K.u 1).1, (K.u 1).2;
    K.h 2, (K.u 2).1, (K.u 2).2]

lemma D3_mul_L0 : D3 K * sideL K 0 = 2 * cross (K.u 1) (K.u 2) := by
  have hS1 := K.sum_u1
  have hS2 := K.sum_u2
  have hh := K.sum_h
  simp only [Fin.sum_univ_three] at hS1 hS2 hh
  simp [D3, Matrix.det_fin_three, sideL, cross]
  linear_combination K.h 1 * ((K.u 2).1 * hS2 - (K.u 2).2 * hS1) +
    K.h 2 * ((K.u 1).2 * hS1 - (K.u 1).1 * hS2) +
    ((K.u 1).1 * (K.u 2).2 - (K.u 1).2 * (K.u 2).1) * hh

lemma D3_ne (hG : GoodSides K) : D3 K ≠ 0 := by
  intro h
  have := D3_mul_L0 (K := K)
  rw [h, zero_mul] at this
  exact tri_cross_ne hG (by decide : (1 : Fin 3) ≠ 2) (by linarith)

variable (K) in
/-- The linear map `(ε, C, Θ) ↦ (H₀, H₁, H₂, Θ)`. -/
noncomputable def Bmat : Matrix (Fin 4) (Fin 4) ℝ :=
  !![K.h 0, (K.u 0).1, (K.u 0).2, 0; K.h 1, (K.u 1).1, (K.u 1).2, 0;
    K.h 2, (K.u 2).1, (K.u 2).2, 0; 0, 0, 0, 1]

lemma det_Bmat : (Bmat K).det = D3 K := by
  rw [Matrix.det_succ_row _ 3]
  simp [Fin.sum_univ_four, Bmat, D3, Matrix.det_fin_three, Matrix.submatrix, Fin.succAbove]
  ring

/-- `∫ G(B v) dv = |det B|⁻¹ ∫ G`. -/
lemma lintegral_comp_mulVec {d : ℕ} (B : Matrix (Fin d) (Fin d) ℝ) (hB : B.det ≠ 0)
    (G : (Fin d → ℝ) → ℝ≥0∞) (hG : Measurable G) :
    (∫⁻ v, G (B *ᵥ v)) = ENNReal.ofReal |B.det|⁻¹ * ∫⁻ w, G w := by
  have hm := Real.map_matrix_volume_pi_eq_smul_volume_pi hB
  have hc : Measurable (Matrix.toLin' B) := (LinearMap.continuous_on_pi _).measurable
  calc (∫⁻ v, G (B *ᵥ v)) = ∫⁻ v, G (Matrix.toLin' B v) := rfl
    _ = ∫⁻ w, G w ∂(Measure.map (Matrix.toLin' B) volume) := (lintegral_map hG hc).symm
    _ = _ := by rw [hm, lintegral_smul_measure, abs_inv]; rfl

variable (K) in
/-- The fitting weight in the coordinates `w = (H₀, H₁, H₂, Θ)`. -/
noncomputable def Gtri (w : Fin 4 → ℝ) : ℝ≥0∞ :=
  ∏ i : Fin 3, {w : Fin 4 → ℝ | w i.castSucc ≤ min (w 3 * K.a i) (w 3 * K.b i)}.indicator
    (fun w => ENNReal.ofReal (Real.exp (sideL K i * w i.castSucc))) w

lemma measurable_Gtri : Measurable (Gtri K) := by
  unfold Gtri
  refine Finset.measurable_prod _ fun i _ => ?_
  exact (ENNReal.measurable_ofReal.comp (Real.continuous_exp.measurable.comp
    (measurable_const.mul (measurable_pi_apply _)))).indicator
      (measurableSet_le (measurable_pi_apply _)
        (((measurable_pi_apply 3).mul_const _).min ((measurable_pi_apply 3).mul_const _)))

lemma fitWeight_eq_Gtri (v : Fin 4 → ℝ) : fitWeight K v = Gtri K (Bmat K *ᵥ v) := by
  have hH : ∀ i : Fin 3, (Bmat K *ᵥ v) i.castSucc = Hs K (copyOfVec v) i := by
    intro i
    fin_cases i <;> simp [Bmat, Matrix.mulVec, dotProduct, Fin.sum_univ_four, Hs, dot,
      copyOfVec] <;> ring
  have h3 : (Bmat K *ᵥ v) 3 = v 3 := by
    simp [Bmat, Matrix.mulVec, dotProduct, Fin.sum_univ_four]
  unfold fitWeight Gtri
  simp only [Set.indicator, mem_ofPred_eq, hH, h3]
  by_cases hF : Fits K (copyOfVec v)
  · rw [if_pos hF]
    have hall : ∀ i : Fin 3, Hs K (copyOfVec v) i ≤ min (v 3 * K.a i) (v 3 * K.b i) := hF
    simp only [hall, if_true]
    rw [← ENNReal.ofReal_prod_of_nonneg (fun i _ => (Real.exp_pos _).le), ← Real.exp_sum]
    congr 2
    rw [sum_L_Hs]; rfl
  · rw [if_neg hF]
    obtain ⟨i, hi⟩ : ∃ i, ¬ Hs K (copyOfVec v) i ≤ min (v 3 * K.a i) (v 3 * K.b i) := by
      by_contra h; push Not at h; exact hF h
    exact (Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)).symm

/-- `∫_{H ≤ c} e^{L H} dH = e^{L c}/L`, as a lower integral. -/
lemma lintegral_exp_Iic' {L : ℝ} (hL : 0 < L) (c : ℝ) :
    ∫⁻ H, (Iic c).indicator (fun H => ENNReal.ofReal (Real.exp (L * H))) H =
      ENNReal.ofReal (Real.exp (L * c) / L) := by
  rw [lintegral_indicator measurableSet_Iic, ← integral_exp_Iic hL c,
    ofReal_integral_eq_lintegral_ofReal (integrableOn_exp_mul_Iic hL c)
      (Filter.Eventually.of_forall fun _ => (Real.exp_pos _).le)]

lemma integrable_exp_neg_abs {c : ℝ} (hc : 0 < c) :
    Integrable fun θ : ℝ => Real.exp (-(c * |θ|)) := by
  rw [← integrableOn_univ, ← Iic_union_Ioi (a := (0 : ℝ))]
  refine IntegrableOn.union ?_ ?_
  · refine (integrableOn_exp_mul_Iic (a := c) hc 0).congr_fun (fun θ hθ => ?_) measurableSet_Iic
    rw [abs_of_nonpos (mem_Iic.1 hθ)]; ring_nf
  · refine (integrableOn_exp_mul_Ioi (a := -c) (by linarith) 0).congr_fun (fun θ hθ => ?_)
      measurableSet_Ioi
    rw [abs_of_pos (mem_Ioi.1 hθ)]; ring_nf

/-- `∫ ∏ φᵢ(wᵢ) dw = ∏ ∫ φᵢ` on `ℝ³`. -/
lemma lintegral_prod_three (φ : Fin 3 → ℝ → ℝ≥0∞) (hφ : ∀ i, Measurable (φ i)) :
    ∫⁻ w : Fin 3 → ℝ, ∏ i, φ i (w i) = ∏ i, ∫⁻ x, φ i x := by
  have hmp : MeasurePreserving (fun s : Fin 3 → ℝ => (s 0, s 1, s 2))
      (Measure.pi fun _ => (volume : Measure ℝ))
      ((volume : Measure ℝ).prod ((volume : Measure ℝ).prod volume)) := by
    have h := ((MeasurePreserving.id (volume : Measure ℝ)).prod
      (measurePreserving_finTwoArrow (volume : Measure ℝ))).comp
      (measurePreserving_piFinSuccAbove (fun _ : Fin 3 => (volume : Measure ℝ)) 0)
    convert h using 1
    funext s
    rfl
  let F : ℝ × ℝ × ℝ → ℝ≥0∞ := fun p => φ 0 p.1 * (φ 1 p.2.1 * φ 2 p.2.2)
  have hF : Measurable F :=
    ((hφ 0).comp measurable_fst).mul (((hφ 1).comp measurable_snd.fst).mul
      ((hφ 2).comp measurable_snd.snd))
  have he : ∀ w : Fin 3 → ℝ, ∏ i, φ i (w i) = F (w 0, w 1, w 2) := by
    intro w; simp only [Fin.prod_univ_three, F, mul_assoc]
  simp_rw [he]
  change ∫⁻ w, F (w 0, w 1, w 2) ∂(Measure.pi fun _ => (volume : Measure ℝ)) = _
  rw [hmp.lintegral_comp hF]
  simp only [F]
  rw [lintegral_prod_mul (f := φ 0) (g := fun q : ℝ × ℝ => φ 1 q.1 * φ 2 q.2) (hφ 0).aemeasurable
    (((hφ 1).comp measurable_fst).mul ((hφ 2).comp measurable_snd)).aemeasurable,
    lintegral_prod_mul (f := φ 1) (g := φ 2) (hφ 1).aemeasurable (hφ 2).aemeasurable,
    Fin.prod_univ_three, mul_assoc]

/-- `∑ Lᵢ min(Θ aᵢ, Θ bᵢ) = -Q |Θ|`. -/
lemma sum_L_min (θ : ℝ) : ∑ i, sideL K i * min (θ * K.a i) (θ * K.b i) = -(Qtri K * |θ|) := by
  rcases le_total 0 θ with h | h
  · have hm : ∀ i, min (θ * K.a i) (θ * K.b i) = θ * K.a i := fun i =>
      min_eq_left (mul_le_mul_of_nonneg_left (K.hab i).le h)
    simp_rw [hm]
    rw [abs_of_nonneg h]
    have := sum_L_a (K := K)
    calc ∑ i, sideL K i * (θ * K.a i) = θ * ∑ i, sideL K i * K.a i := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
      _ = -(Qtri K * θ) := by rw [this]; ring
  · have hm : ∀ i, min (θ * K.a i) (θ * K.b i) = θ * K.b i := fun i =>
      min_eq_right (mul_le_mul_of_nonpos_left (K.hab i).le h)
    simp_rw [hm]
    rw [abs_of_nonpos h]
    have := sum_L_b (K := K)
    calc ∑ i, sideL K i * (θ * K.b i) = θ * ∑ i, sideL K i * K.b i := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
      _ = -(Qtri K * -θ) := by rw [this]; ring

lemma lintegral_Gtri : ∫⁻ w, Gtri K w =
    ENNReal.ofReal (2 / (Qtri K * (sideL K 0 * sideL K 1 * sideL K 2))) := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin 4 => ℝ) (Fin.last 3)
  have he : MeasurePreserving e volume volume :=
    volume_preserving_piFinSuccAbove (fun _ : Fin 4 => ℝ) (Fin.last 3)
  rw [← he.symm.lintegral_comp_emb e.symm.measurableEmbedding, Measure.volume_eq_prod,
    lintegral_prod (fun a => Gtri K (e.symm a)) (measurable_Gtri.comp e.symm.measurable).aemeasurable]
  -- the integrand at `(Θ, H)`
  have hpt : ∀ (θ : ℝ) (H : Fin 3 → ℝ), Gtri K (e.symm (θ, H)) = ∏ i : Fin 3,
      (Iic (min (θ * K.a i) (θ * K.b i))).indicator
        (fun x => ENNReal.ofReal (Real.exp (sideL K i * x))) (H i) := by
    intro θ H
    have h3 : (e.symm (θ, H)) 3 = θ := by
      simp [e, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNth_apply_same]
    have hc : ∀ i : Fin 3, (e.symm (θ, H)) i.castSucc = H i := by
      intro i
      rw [← Fin.succAbove_last]
      simp [e, MeasurableEquiv.piFinSuccAbove_symm_apply]
    unfold Gtri
    refine Finset.prod_congr rfl fun i _ => ?_
    simp only [Set.indicator, mem_ofPred_eq, mem_Iic, hc, h3]
  have hinner : ∀ θ : ℝ, ∫⁻ H : Fin 3 → ℝ, Gtri K (e.symm (θ, H)) =
      ENNReal.ofReal (Real.exp (-(Qtri K * |θ|)) / (sideL K 0 * sideL K 1 * sideL K 2)) := by
    intro θ
    simp_rw [hpt]
    rw [lintegral_prod_three (fun i x => (Iic (min (θ * K.a i) (θ * K.b i))).indicator
      (fun x => ENNReal.ofReal (Real.exp (sideL K i * x))) x) fun i => (ENNReal.measurable_ofReal.comp
      (Real.continuous_exp.measurable.comp (measurable_const.mul measurable_id))).indicator
        measurableSet_Iic]
    simp_rw [lintegral_exp_Iic' (sideL_pos _)]
    rw [← ENNReal.ofReal_prod_of_nonneg (fun i _ => div_nonneg (Real.exp_pos _).le
      (sideL_pos i).le), Fin.prod_univ_three]
    congr 1
    rw [← sum_L_min θ, Fin.sum_univ_three, Real.exp_add, Real.exp_add]
    field_simp
  simp_rw [hinner]
  have hL : 0 < sideL K 0 * sideL K 1 * sideL K 2 := by
    have := sideL_pos (K := K) 0; have := sideL_pos (K := K) 1; have := sideL_pos (K := K) 2
    positivity
  rw [← ofReal_integral_eq_lintegral_ofReal
    ((integrable_exp_neg_abs Qtri_pos).div_const _)
    (Filter.Eventually.of_forall fun θ => div_nonneg (Real.exp_pos _).le hL.le),
    integral_div, integral_exp_neg_abs Qtri_pos]
  congr 1
  field_simp

/-- **The spatial factor of a triangle**: `∫ fitWeight = 2 / (|D₃| Q L₀ L₁ L₂)`. -/
theorem fit_integral_triangle (hG : GoodSides K) :
    ∫⁻ v, fitWeight K v = ENNReal.ofReal |D3 K|⁻¹ *
      ENNReal.ofReal (2 / (Qtri K * (sideL K 0 * sideL K 1 * sideL K 2))) := by
  have hB : (Bmat K).det ≠ 0 := by rw [det_Bmat]; exact D3_ne hG
  simp_rw [fitWeight_eq_Gtri]
  rw [lintegral_comp_mulVec _ hB _ measurable_Gtri, det_Bmat]
  congr 1
  exact lintegral_Gtri
end Enclosing
