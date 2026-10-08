import EnclosingCopy.Enclosing.VertexEvent
import Mathlib.MeasureTheory.Group.Arithmetic

/-!
# The vertex factors in geometric coordinates

The four-dimensional fitting integral is the paper's integral over nonnegative
scale `t`, tilt `θ`, and the area of the allowed translation region `R(t, θ)`.
The transformation preserves Lebesgue measure, and fitting forces `ε ≤ 0`,
which justifies restricting `t = -ε` to nonnegative values.

The inverse-matrix certificate used in the candidate code also agrees with
the existential positive-row-combination condition in the geometric formula.
The limiting probability here is the certified vertex-candidate event, not
the complete vertex/segment probability or a finite-iid-sample limit.
-/

namespace Enclosing
open MeasureTheory Set ENNReal
variable {m : ℕ} (K : Sides m)

def fittingRegion (t θ : ℝ) : Set (ℝ × ℝ) :=
  {C | ∀ i, dot C (K.u i) ≤ t * K.h i + min (θ * K.a i) (θ * K.b i)}

lemma measurableSet_fittingRegion (t θ : ℝ) : MeasurableSet (fittingRegion K t θ) := by
  simp only [fittingRegion, ofPred_forall]
  apply MeasurableSet.iInter
  intro i
  exact measurableSet_le (by unfold dot; fun_prop) measurable_const

lemma fits_iff_region (ε θ : ℝ) (C : ℝ × ℝ) :
    Fits K (ε, C, θ) ↔ C ∈ fittingRegion K (-ε) θ := by
  constructor <;> intro h i
  · have hi := h i
    change ε * K.h i + dot C (K.u i) ≤ _ at hi
    change dot C (K.u i) ≤ _
    linarith
  · have hi := h i
    change dot C (K.u i) ≤ _ at hi
    change ε * K.h i + dot C (K.u i) ≤ _
    linarith

lemma fits_scale_nonpos (z : Copy) (hz : Fits K z) : z.1 ≤ 0 := by
  have hnn : 0 ≤ -(2 * z.1) := by
    rw [← sum_line_area K z]
    exact Finset.sum_nonneg fun i _ => line_area_nonneg (K.hab i).le (hz i)
  linarith

noncomputable def copyEquiv : (Fin 4 → ℝ) ≃ᵐ Copy where
  toFun := copyOfVec
  invFun := zvec
  left_inv := zvec_copyOfVec
  right_inv := copyOfVec_zvec
  measurable_toFun := measurable_copyOfVec
  measurable_invFun := by
    change Measurable zvec
    apply Measurable.of_eval
    intro i
    fin_cases i <;> simp only [zvec] <;> fun_prop

lemma copyEquiv_preserving : MeasurePreserving copyEquiv := by
  let e0 := MeasurableEquiv.piFinSuccAbove (fun _ : Fin 4 => ℝ) (0 : Fin 4)
  let e3 := MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) (Fin.last 2)
  let e2 := MeasurableEquiv.piFinTwo (fun _ : Fin 2 => ℝ)
  have h0 : MeasurePreserving e0 := volume_preserving_piFinSuccAbove _ _
  have h3 : MeasurePreserving e3 := volume_preserving_piFinSuccAbove _ _
  have h2 : MeasurePreserving e2 := volume_preserving_piFinTwo _
  have h32 : MeasurePreserving ((MeasurableEquiv.refl ℝ).prodCongr e2) :=
    (MeasurePreserving.id (volume : Measure ℝ)).prod h2
  have hswap : MeasurePreserving (MeasurableEquiv.prodComm : (ℝ × (ℝ × ℝ)) ≃ᵐ ((ℝ × ℝ) × ℝ)) :=
    Measure.measurePreserving_swap
  have h : MeasurePreserving
      (fun v : Fin 4 → ℝ => (v 0, (v 1, v 2), v 3)) := by
    convert ((MeasurePreserving.id (volume : Measure ℝ)).prod
      (hswap.comp (h32.comp h3))).comp h0 using 1
    funext v
    rfl
  exact h

noncomputable def copyWeight (z : Copy) : ℝ≥0∞ := fitWeight K (zvec z)

lemma measurable_copyWeight : Measurable (copyWeight K) :=
  (measurable_fitWeight K).comp copyEquiv.symm.measurable

lemma translation_weight_integral (ε θ : ℝ) :
    (∫⁻ C : ℝ × ℝ, copyWeight K (ε, C, θ)) =
      ENNReal.ofReal (Real.exp (2 * ε)) * volume (fittingRegion K (-ε) θ) := by
  have he : (fun C : ℝ × ℝ => copyWeight K (ε, C, θ)) =
      (fittingRegion K (-ε) θ).indicator (fun _ => ENNReal.ofReal (Real.exp (2 * ε))) := by
    funext C
    change {v | Fits K (copyOfVec v)}.indicator
      (fun v => ENNReal.ofReal (Real.exp (2 * v 0))) (zvec (ε, C, θ)) = _
    have h := fits_iff_region K ε θ C
    by_cases hc : C ∈ fittingRegion K (-ε) θ
    · have hf : zvec (ε, C, θ) ∈ {v | Fits K (copyOfVec v)} := by
        simpa only [mem_ofPred_eq, copyOfVec_zvec] using h.mpr hc
      rw [indicator_of_mem hf, indicator_of_mem hc]; rfl
    · have hf : zvec (ε, C, θ) ∉ {v | Fits K (copyOfVec v)} := by
        simpa only [mem_ofPred_eq, copyOfVec_zvec] using mt h.mp hc
      rw [indicator_of_notMem hf, indicator_of_notMem hc]
  rw [he, lintegral_indicator_const (measurableSet_fittingRegion K _ _)]

lemma fit_integral_coordinates :
    (∫⁻ v : Fin 4 → ℝ, fitWeight K v) =
      ∫⁻ θ : ℝ, ∫⁻ ε : ℝ,
        ENNReal.ofReal (Real.exp (2 * ε)) * volume (fittingRegion K (-ε) θ) := by
  have hW := measurable_copyWeight K
  have hj : Measurable (fun q : (ℝ × ℝ) × (ℝ × ℝ) => copyWeight K (q.1.1, q.2, q.1.2)) :=
    hW.comp (measurable_fst.fst.prodMk (measurable_snd.prodMk measurable_fst.snd))
  calc (∫⁻ v : Fin 4 → ℝ, fitWeight K v)
      = ∫⁻ z : Copy, copyWeight K z := by
        have h := copyEquiv_preserving.lintegral_comp_emb copyEquiv.measurableEmbedding (copyWeight K)
        simpa only [copyWeight, copyEquiv, MeasurableEquiv.coe_mk, Equiv.coe_fn_mk,
          zvec_copyOfVec] using h
    _ = ∫⁻ ε : ℝ, ∫⁻ p : (ℝ × ℝ) × ℝ, copyWeight K (ε, p) :=
      lintegral_prod _ hW.aemeasurable
    _ = ∫⁻ ε : ℝ, ∫⁻ θ : ℝ, ∫⁻ C : ℝ × ℝ, copyWeight K (ε, C, θ) := by
      apply lintegral_congr
      intro ε
      exact lintegral_prod_symm _ (hW.comp (measurable_const.prodMk measurable_id)).aemeasurable
    _ = ∫⁻ θ : ℝ, ∫⁻ ε : ℝ, ∫⁻ C : ℝ × ℝ, copyWeight K (ε, C, θ) :=
      lintegral_lintegral_swap hj.lintegral_prod_right'.aemeasurable
    _ = _ := by
      apply lintegral_congr; intro θ
      apply lintegral_congr; intro ε
      exact translation_weight_integral K ε θ

lemma fittingRegion_empty_of_neg {t : ℝ} (ht : t < 0) (θ : ℝ) : fittingRegion K t θ = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro C hc
  have hf : Fits K (-t, C, θ) := (fits_iff_region K (-t) θ C).mpr (by simpa using hc)
  have h := fits_scale_nonpos K _ hf
  change -t ≤ 0 at h
  linarith

/-- The geometric fitting integral in the paper's coordinates: scale `t ≥ 0`,
tilt `θ`, and the area of allowed translations. -/
noncomputable def spatialVertexIntegral : ℝ≥0∞ :=
  ∫⁻ θ : ℝ, ∫⁻ t : ℝ in Ici 0,
    ENNReal.ofReal (Real.exp (-2 * t)) * volume (fittingRegion K t θ)

theorem fit_integral_eq_spatial :
    (∫⁻ v : Fin 4 → ℝ, fitWeight K v) = spatialVertexIntegral K := by
  rw [fit_integral_coordinates]
  apply lintegral_congr
  intro θ
  have hneg := (Measure.measurePreserving_neg (volume : Measure ℝ)).lintegral_comp_emb
    (Homeomorph.neg ℝ).measurableEmbedding
    (fun ε : ℝ => ENNReal.ofReal (Real.exp (2 * ε)) * volume (fittingRegion K (-ε) θ))
  have he : (∫⁻ ε : ℝ, ENNReal.ofReal (Real.exp (2 * ε)) * volume (fittingRegion K (-ε) θ)) =
      ∫⁻ t : ℝ, ENNReal.ofReal (Real.exp (-2 * t)) * volume (fittingRegion K t θ) := by
    simpa only [neg_neg, mul_neg, neg_mul] using hneg.symm
  rw [he]
  rw [← lintegral_indicator measurableSet_Ici]
  apply lintegral_congr
  intro t
  by_cases ht : t ∈ Ici (0 : ℝ)
  · rw [indicator_of_mem ht]
  · rw [indicator_of_notMem ht, fittingRegion_empty_of_neg K (lt_of_not_ge ht) θ,
      measure_empty, mul_zero]

theorem vertex_candidate_prob_spatial_limit :
    Filter.Tendsto (fun n : ℕ => PoissonPP.law (Λ K n) {ω | HasVertexCandidate K n ω})
      Filter.atTop (nhds (vertexDensity K * spatialVertexIntegral K)) := by
  rw [← fit_integral_eq_spatial K]
  exact vertex_candidate_prob_limit K

def vertexConeCondition (k : Fin 4 → Fin m) (s : Fin 4 → ℝ) : Prop :=
  ∃ l : Fin 4 → ℝ, (∀ r, 0 < l r) ∧
    ∀ c, ∑ r, l r * row K (pointsOf k s 0 r) c = if c = 0 then 1 else 0

lemma rowGood_iff_cone (k : Fin 4 → Fin m) (s : Fin 4 → ℝ) :
    RowGood K k s ↔ (vertexMatrix K (pointsOf k s 0)).det ≠ 0 ∧ vertexConeCondition K k s := by
  constructor
  · intro h
    exact ⟨h.1, vertexCert K (pointsOf k s 0), h.2, vertexCert_eq K _ h.1⟩
  · rintro ⟨hA, l, hl, he⟩
    refine ⟨hA, ?_⟩
    rw [vertexCert_eq_of_certificate K _ hA l he]
    exact hl

noncomputable def coneVertexDensity : ℝ≥0∞ :=
  (1 / 24) * ∑ k : Fin 4 → Fin m,
    ∫⁻ s, ENNReal.ofReal
      ({s | vertexConeCondition K k s}.indicator
        (fun s => |(vertexMatrix K (pointsOf k s 0)).det|) s)
      ∂(Measure.pi fun r => volume.restrict (Icc (K.a (k r)) (K.b (k r))))

lemma rowDensity_eq_cone (k : Fin 4 → Fin m) (s : Fin 4 → ℝ) :
    rowDensity K k s = ENNReal.ofReal
      ({s | vertexConeCondition K k s}.indicator
        (fun s => |(vertexMatrix K (pointsOf k s 0)).det|) s) := by
  by_cases hA : (vertexMatrix K (pointsOf k s 0)).det = 0
  · have hg : ¬ RowGood K k s := fun h => h.1 hA
    rw [rowDensity, indicator_of_notMem (show s ∉ {s | RowGood K k s} from hg)]
    by_cases hc : vertexConeCondition K k s
    · rw [indicator_of_mem (show s ∈ {s | vertexConeCondition K k s} from hc), hA,
        abs_zero, ENNReal.ofReal_zero]
    · rw [indicator_of_notMem (show s ∉ {s | vertexConeCondition K k s} from hc),
        ENNReal.ofReal_zero]
  · by_cases hc : vertexConeCondition K k s
    · have hg := (rowGood_iff_cone K k s).mpr ⟨hA, hc⟩
      rw [rowDensity, indicator_of_mem (show s ∈ {s | RowGood K k s} from hg),
        indicator_of_mem (show s ∈ {s | vertexConeCondition K k s} from hc)]
    · have hg : ¬ RowGood K k s := fun h => hc ((rowGood_iff_cone K k s).mp h).2
      rw [rowDensity, indicator_of_notMem (show s ∉ {s | RowGood K k s} from hg),
        indicator_of_notMem (show s ∉ {s | vertexConeCondition K k s} from hc),
        ENNReal.ofReal_zero]

theorem vertexDensity_eq_cone : vertexDensity K = coneVertexDensity K := by
  unfold vertexDensity coneVertexDensity
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  apply lintegral_congr
  exact rowDensity_eq_cone K k

/-- The complete vertex-candidate limit with its geometric area and cone-density factors. -/
theorem vertex_candidate_formula_limit :
    Filter.Tendsto (fun n : ℕ => PoissonPP.law (Λ K n) {ω | HasVertexCandidate K n ω})
      Filter.atTop (nhds (spatialVertexIntegral K * coneVertexDensity K)) := by
  rw [mul_comm, ← vertexDensity_eq_cone K]
  exact vertex_candidate_prob_spatial_limit K

end Enclosing
