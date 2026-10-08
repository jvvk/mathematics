import EnclosingCopy.Enclosing.LP
import Mathlib.Analysis.Matrix.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Lebesgue.Add

/-!
# Four-point vertex candidates in the Poisson strip model

This module supplies the Mecke/change-of-variables part of the vertex computation.
`vertex_count_factor` factors the expected unordered candidate count at depth cutoff `T`
into its row density and spatial fitting integral. `vertex_count_limit` removes the cutoff.
Candidates have an invertible tight matrix and a strictly positive optimality certificate;
`vertexGood_unique` proves the corresponding deterministic uniqueness assertion.

These are candidate-count theorems. `VertexEvent` converts them into genuine
vertex-candidate probabilities, and `VertexSpatial` supplies the geometric-coordinate
formula. The full optimum classification (GeneralClassify) and finite-sample convergence
(Theorem1) are proved separately; neither is assumed here.
-/

namespace Enclosing
open MeasureTheory Set Matrix ENNReal
variable {m : ℕ} (K : Sides m)

def copyOfVec (v : Fin 4 → ℝ) : Copy := (v 0, (v 1, v 2), v 3)

lemma zvec_copyOfVec (v : Fin 4 → ℝ) : zvec (copyOfVec v) = v := by
  ext i; fin_cases i <;> rfl

lemma copyOfVec_zvec (z : Copy) : copyOfVec (zvec z) = z := rfl

def vertexMatrix (x : Fin 4 → Pt m) : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.of fun r => row K (x r)

noncomputable def vertexCopy (x : Fin 4 → Pt m) : Copy :=
  copyOfVec ((vertexMatrix K x)⁻¹ *ᵥ (fun r => -(x r).2.2))

noncomputable def vertexCert (x : Fin 4 → Pt m) : Fin 4 → ℝ :=
  (Pi.single 0 1) ᵥ* (vertexMatrix K x)⁻¹

def Fits (z : Copy) : Prop :=
  ∀ i, Hs K z i ≤ min (z.2.2 * K.a i) (z.2.2 * K.b i)

def Below (T : ℝ) (z : Copy) : Prop :=
  ∀ i, max (z.2.2 * K.a i) (z.2.2 * K.b i) - Hs K z i ≤ T

def VertexGood (T : ℝ) (x : Fin 4 → Pt m) : Prop :=
  (vertexMatrix K x).det ≠ 0 ∧ (∀ r, 0 < vertexCert K x r) ∧
    Fits K (vertexCopy K x) ∧ Below K T (vertexCopy K x)

lemma vertexCopy_tight (x : Fin 4 → Pt m) (hA : (vertexMatrix K x).det ≠ 0) :
    ∀ r, gx K (vertexCopy K x) (x r) = 0 := by
  have h := Matrix.mul_nonsing_inv (vertexMatrix K x) (isUnit_iff_ne_zero.mpr hA)
  have he : vertexMatrix K x *ᵥ zvec (vertexCopy K x) = fun r => -(x r).2.2 := by
    rw [vertexCopy, zvec_copyOfVec, Matrix.mulVec_mulVec, h, Matrix.one_mulVec]
  intro r
  have hr := congrFun he r
  rw [gx_eq]
  change (vertexMatrix K x *ᵥ zvec (vertexCopy K x)) r + (x r).2.2 = 0
  rw [hr]; ring

lemma vertexCert_eq (x : Fin 4 → Pt m) (hA : (vertexMatrix K x).det ≠ 0) :
    ∀ c, ∑ r, vertexCert K x r * row K (x r) c = if c = 0 then 1 else 0 := by
  have h := Matrix.nonsing_inv_mul (vertexMatrix K x) (isUnit_iff_ne_zero.mpr hA)
  have he : vertexCert K x ᵥ* vertexMatrix K x = Pi.single 0 1 := by
    rw [vertexCert, Matrix.vecMul_vecMul, h, Matrix.vecMul_one]
  intro c
  simpa [Matrix.vecMul, dotProduct, vertexMatrix, Pi.single_apply, eq_comm] using congrFun he c

lemma measurable_vertexMatrix : Measurable (vertexMatrix K) := by
  apply Measurable.of_eval_matrix
  intro r c
  fin_cases c
  · exact (measurable_of_countable K.h).comp (measurable_fst.comp (measurable_pi_apply r))
  · exact (measurable_of_countable fun i => (K.u i).1).comp
      (measurable_fst.comp (measurable_pi_apply r))
  · exact (measurable_of_countable fun i => (K.u i).2).comp
      (measurable_fst.comp (measurable_pi_apply r))
  · exact ((measurable_fst.comp measurable_snd).comp (measurable_pi_apply r)).neg

lemma measurable_matrixInv : Measurable (fun A : Matrix (Fin 4) (Fin 4) ℝ => A⁻¹) := by
  simp_rw [Matrix.inv_def, Ring.inverse_eq_inv]
  exact continuous_id.matrix_det.measurable.inv.smul continuous_id.matrix_adjugate.measurable

lemma measurable_vertexCopy : Measurable (vertexCopy K) := by
  have hI := measurable_matrixInv.comp (measurable_vertexMatrix K)
  have hv : Measurable (fun x : Fin 4 → Pt m =>
      (vertexMatrix K x)⁻¹ *ᵥ (fun r => -(x r).2.2)) := by
    apply Measurable.of_eval
    intro c
    unfold Matrix.mulVec dotProduct
    exact Finset.measurable_sum _ fun r _ =>
      (hI.eval_matrix).mul (((measurable_snd.comp measurable_snd).comp
        (measurable_pi_apply r)).neg)
  exact ((measurable_pi_apply 0).prodMk
    (((measurable_pi_apply 1).prodMk (measurable_pi_apply 2)).prodMk
      (measurable_pi_apply 3))).comp hv

lemma measurable_vertexCert : Measurable (vertexCert K) := by
  have hI := measurable_matrixInv.comp (measurable_vertexMatrix K)
  apply Measurable.of_eval
  intro c
  unfold vertexCert Matrix.vecMul dotProduct
  exact Finset.measurable_sum _ fun r _ => measurable_const.mul hI.eval_matrix

lemma measurable_Hs (i : Fin m) : Measurable (fun z : Copy => Hs K z i) := by
  unfold Hs dot
  fun_prop

lemma measurableSet_Fits : MeasurableSet {z | Fits K z} := by
  simp only [Fits, ofPred_forall]
  exact MeasurableSet.iInter fun i => measurableSet_le (measurable_Hs K i)
    (((measurable_snd.comp measurable_snd).mul_const (K.a i)).min
      ((measurable_snd.comp measurable_snd).mul_const (K.b i)))

lemma measurableSet_Below (T : ℝ) : MeasurableSet {z | Below K T z} := by
  simp only [Below, ofPred_forall]
  exact MeasurableSet.iInter fun i => measurableSet_le
    ((((measurable_snd.comp measurable_snd).mul_const (K.a i)).max
      ((measurable_snd.comp measurable_snd).mul_const (K.b i))).sub
      (measurable_Hs K i)) measurable_const

lemma measurableSet_VertexGood (T : ℝ) : MeasurableSet {x | VertexGood K T x} := by
  have hdet := continuous_id.matrix_det.measurable.comp (measurable_vertexMatrix K)
  have hc : MeasurableSet {x | ∀ r, 0 < vertexCert K x r} := by
    simp only [ofPred_forall]
    exact MeasurableSet.iInter fun r => measurableSet_lt measurable_const
      ((measurable_pi_apply r).comp (measurable_vertexCert K))
  exact (measurableSet_eq_fun hdet measurable_const).compl.inter
    (hc.inter
        (((measurableSet_Fits K).preimage (measurable_vertexCopy K)).inter
          ((measurableSet_Below K T).preimage (measurable_vertexCopy K))))

lemma below_line (T : ℝ) (z : Copy) (hz : Below K T z) (i : Fin m)
    {s : ℝ} (hs : s ∈ Icc (K.a i) (K.b i)) : z.2.2 * s - Hs K z i ≤ T := by
  have hbound : z.2.2 * s ≤ max (z.2.2 * K.a i) (z.2.2 * K.b i) := by
    by_cases h : 0 ≤ z.2.2
    · exact (mul_le_mul_of_nonneg_left hs.2 h).trans (le_max_right _ _)
    · exact (mul_le_mul_of_nonpos_left hs.1 (le_of_not_ge h)).trans (le_max_left _ _)
  exact (sub_le_sub_right hbound _).trans (hz i)

lemma vertexGood_void (T : ℝ) (x : Fin 4 → Pt m) (hx : VertexGood K T x) :
    PoissonPP.prob (Λ K T) (fun μ => Feasible K μ (vertexCopy K x)) =
      ENNReal.ofReal (Real.exp (2 * (vertexCopy K x).1)) :=
  model_void K T _ hx.2.2.1 (fun i _s hs => below_line K T _ hx.2.2.2 i hs)

lemma vertexGood_optimal (T : ℝ) (x : Fin 4 → Pt m) (hx : VertexGood K T x)
    (z : Copy) (hz : ∀ r, 0 ≤ gx K z (x r)) : (vertexCopy K x).1 ≤ z.1 :=
  vertex_optimal K x (vertexCert K x) hx.2.1 (vertexCert_eq K x hx.1) _
    (vertexCopy_tight K x hx.1) z hz

lemma vertexGood_unique (T : ℝ) (x : Fin 4 → Pt m) (hx : VertexGood K T x)
    (z : Copy) (hz : ∀ r, 0 ≤ gx K z (x r)) (he : z.1 = (vertexCopy K x).1) :
    z = vertexCopy K x := by
  have h := vertex_unique K x (vertexCert K x) hx.2.1 (vertexCert_eq K x hx.1)
    hx.1 _ (vertexCopy_tight K x hx.1) z hz he
  exact congrArg copyOfVec h

lemma measurableSet_vertexViolation :
    MeasurableSet {q : (Fin 4 → Pt m) × Pt m | q.2 ∈ Vz K (vertexCopy K q.1)} := by
  have hz : Measurable (fun q : (Fin 4 → Pt m) × Pt m => vertexCopy K q.1) :=
    (measurable_vertexCopy K).comp measurable_fst
  have hi : Measurable (fun q : (Fin 4 → Pt m) × Pt m => q.2.1) :=
    measurable_fst.comp measurable_snd
  have hs : Measurable (fun q : (Fin 4 → Pt m) × Pt m => q.2.2.1) :=
    (measurable_fst.comp measurable_snd).comp measurable_snd
  have hD : Measurable (fun q : (Fin 4 → Pt m) × Pt m => q.2.2.2) :=
    (measurable_snd.comp measurable_snd).comp measurable_snd
  have hH : Measurable (fun q : (Fin 4 → Pt m) × Pt m => Hs K (vertexCopy K q.1) q.2.1) := by
    unfold Hs dot
    exact (hz.fst.mul ((measurable_of_countable K.h).comp hi)).add
      (((hz.snd.fst.fst).mul ((measurable_of_countable fun i => (K.u i).1).comp hi)).add
        ((hz.snd.fst.snd).mul ((measurable_of_countable fun i => (K.u i).2).comp hi)))
  exact measurableSet_lt hD ((hz.snd.snd.mul hs).sub hH)

/-- The ordered four-point candidate count, with a void condition on all remaining points. -/
noncomputable def vertexOrderedCount (T : ℝ) : ℝ≥0∞ :=
  ∑' n : ℕ, PoissonPP.w0 (Λ K T) / n.factorial *
    ∫⁻ y : Fin n → Pt m, ∑ i : Fin 4 ↪ Fin n,
      {x | VertexGood K T x}.indicator (1 : (Fin 4 → Pt m) → ℝ≥0∞) (y ∘ i) *
        {μ | Feasible K μ (vertexCopy K (y ∘ i))}.indicator 1 (PoissonPP.rest y i)
      ∂(Measure.pi fun _ => Λ K T)

/-- The four-point Mecke bridge with the actual LP copy and its void probability.
This counts candidates. `VertexEvent` proves the corresponding probability bridge;
the full optimum classification is in `GeneralClassify`. -/
theorem vertex_mecke (T : ℝ) :
    vertexOrderedCount K T =
      ∫⁻ x : Fin 4 → Pt m, {x | VertexGood K T x}.indicator
        (fun x => ENNReal.ofReal (Real.exp (2 * (vertexCopy K x).1))) x
        ∂(Measure.pi fun _ => Λ K T) := by
  have h := PoissonPP.mecke_void (Λ K T) 4
    ({x | VertexGood K T x}.indicator (1 : (Fin 4 → Pt m) → ℝ≥0∞))
    (fun x => Vz K (vertexCopy K x))
    (measurable_one.indicator (measurableSet_VertexGood K T))
    (measurableSet_vertexViolation K)
  change vertexOrderedCount K T = _ at h
  rw [h]
  refine lintegral_congr fun x => ?_
  by_cases hx : VertexGood K T x
  · have hx' : x ∈ {x | VertexGood K T x} := hx
    rw [indicator_of_mem hx', indicator_of_mem hx', Pi.one_apply, one_mul,
      Λ_Vz K T _ hx.2.2.1 (fun i s hs => below_line K T _ hx.2.2.2 i hs)]
    have hnn : 0 ≤ -(2 * (vertexCopy K x).1) := by
      rw [← sum_line_area K (vertexCopy K x)]
      exact Finset.sum_nonneg fun i _ => line_area_nonneg (K.hab i).le (hx.2.2.1 i)
    rw [ENNReal.toReal_ofReal hnn]
    congr 2; ring
  · have hx' : x ∉ {x | VertexGood K T x} := hx
    rw [indicator_of_notMem hx', indicator_of_notMem hx', zero_mul]

/-- The depth-to-copy map has Jacobian `|det A|` (the dimension is four). -/
theorem lintegral_depths (A : Matrix (Fin 4) (Fin 4) ℝ) (hA : A.det ≠ 0)
    (f : (Fin 4 → ℝ) → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ D : Fin 4 → ℝ, f (A⁻¹ *ᵥ (-D))) =
      ENNReal.ofReal |A.det| * ∫⁻ z : Fin 4 → ℝ, f z := by
  have hd : (-A⁻¹).det = A.det⁻¹ := by
    simp [Matrix.det_neg, Matrix.det_nonsing_inv, Ring.inverse_eq_inv]
    norm_num
  have hb : (-A⁻¹).det ≠ 0 := by rw [hd]; exact inv_ne_zero hA
  have hm := Real.map_matrix_volume_pi_eq_smul_volume_pi hb
  have hc : Measurable (Matrix.toLin' (-A⁻¹)) :=
    (LinearMap.continuous_on_pi _).measurable
  have hs : ENNReal.ofReal |((-A⁻¹).det)⁻¹| = ENNReal.ofReal |A.det| := by
    rw [hd, inv_inv]
  calc (∫⁻ D : Fin 4 → ℝ, f (A⁻¹ *ᵥ (-D)))
      = ∫⁻ D : Fin 4 → ℝ, f (Matrix.toLin' (-A⁻¹) D) := by
        congr 1; funext D
        rw [Matrix.toLin'_apply, Matrix.neg_mulVec, Matrix.mulVec_neg]
    _ = ∫⁻ z : Fin 4 → ℝ, f z ∂(Measure.map (Matrix.toLin' (-A⁻¹)) volume) :=
      (lintegral_map hf hc).symm
    _ = _ := by rw [hm, lintegral_smul_measure, hs]; rfl

noncomputable def fitWeight (z : Fin 4 → ℝ) : ℝ≥0∞ :=
  {z | Fits K (copyOfVec z)}.indicator (fun z => ENNReal.ofReal (Real.exp (2 * z 0))) z

noncomputable def fitWeightBelow (T : ℝ) (z : Fin 4 → ℝ) : ℝ≥0∞ :=
  {z | Below K T (copyOfVec z)}.indicator (fitWeight K) z

lemma measurable_copyOfVec : Measurable copyOfVec :=
  (measurable_pi_apply 0).prodMk
    (((measurable_pi_apply 1).prodMk (measurable_pi_apply 2)).prodMk (measurable_pi_apply 3))

lemma measurable_fitWeight : Measurable (fitWeight K) := by
  unfold fitWeight
  exact (ENNReal.measurable_ofReal.comp
    ((Real.continuous_exp.measurable).comp
      (measurable_const.mul (measurable_pi_apply 0)))).indicator
        ((measurableSet_Fits K).preimage measurable_copyOfVec)

lemma measurable_fitWeightBelow (T : ℝ) : Measurable (fitWeightBelow K T) :=
  (measurable_fitWeight K).indicator ((measurableSet_Below K T).preimage measurable_copyOfVec)

lemma below_mono {T U : ℝ} (h : T ≤ U) (z : Copy) : Below K T z → Below K U z := by
  intro hz i; exact (hz i).trans h

lemma exists_below (z : Copy) : ∃ n : ℕ, Below K n z := by
  have hn : ∀ i, ∃ n : ℕ, max (z.2.2 * K.a i) (z.2.2 * K.b i) - Hs K z i ≤ n := by
    intro i; obtain ⟨n, hn⟩ := exists_nat_ge (max (z.2.2 * K.a i) (z.2.2 * K.b i) - Hs K z i)
    exact ⟨n, hn⟩
  choose n hn using hn
  refine ⟨∑ i, n i, fun i => (hn i).trans ?_⟩
  exact_mod_cast Finset.single_le_sum (fun j _ => Nat.zero_le (n j)) (Finset.mem_univ i)

lemma fitWeightBelow_mono (z : Fin 4 → ℝ) : Monotone (fun n : ℕ => fitWeightBelow K n z) := by
  intro n q hnq
  by_cases hn : Below K n (copyOfVec z)
  · have hq := below_mono K (T := (n : ℝ)) (U := (q : ℝ)) (by exact_mod_cast hnq) _ hn
    simp only [fitWeightBelow, indicator_of_mem (show z ∈ {z | Below K n (copyOfVec z)} from hn),
      indicator_of_mem (show z ∈ {z | Below K q (copyOfVec z)} from hq)]
    exact le_rfl
  · simp only [fitWeightBelow,
      indicator_of_notMem (show z ∉ {z | Below K n (copyOfVec z)} from hn)]
    exact bot_le

/-- Removing the depth cutoff in the copy integral, by monotone convergence. -/
theorem fit_integral_limit :
    Filter.Tendsto (fun n : ℕ => ∫⁻ z, fitWeightBelow K n z) Filter.atTop
      (nhds (∫⁻ z, fitWeight K z)) := by
  refine lintegral_tendsto_of_tendsto_of_monotone
    (fun n => (measurable_fitWeightBelow K n).aemeasurable)
    (Filter.Eventually.of_forall (fitWeightBelow_mono K)) ?_
  apply Filter.Eventually.of_forall
  intro z
  obtain ⟨n, hn⟩ := exists_below K (copyOfVec z)
  apply Filter.Tendsto.congr' (f₁ := fun _ : ℕ => fitWeight K z) _ tendsto_const_nhds
  filter_upwards [Filter.eventually_ge_atTop n] with q hq
  unfold fitWeightBelow
  exact (indicator_of_mem (f := fitWeight K)
    (show z ∈ {z | Below K q (copyOfVec z)} from
      below_mono K (T := (n : ℝ)) (U := (q : ℝ)) (by exact_mod_cast hq) _ hn)).symm

lemma intensity_pi_eq (T : ℝ) :
    (Measure.pi fun _ : Fin 4 => Λ K T) =
      ∑ k : Fin 4 → Fin m, Measure.pi fun r =>
        (Measure.dirac (k r)).prod
          (volume.restrict (Icc (K.a (k r)) (K.b (k r)) ×ˢ Icc (0 : ℝ) T)) := by
  apply Measure.pi_eq
  intro s hs
  rw [Measure.coe_finsetSum, Finset.sum_apply]
  simp_rw [Measure.pi_pi, Λ, Measure.coe_finsetSum, Finset.sum_apply]
  exact (Fintype.prod_sum (fun (r : Fin 4) (i : Fin m) =>
    ((Measure.dirac i).prod
      (volume.restrict (Icc (K.a i) (K.b i) ×ˢ Icc (0 : ℝ) T))) (s r))).symm

lemma pi_dirac_tuple (k : Fin 4 → Fin m) :
    (Measure.pi fun r => Measure.dirac (k r)) = Measure.dirac k := by
  apply Measure.pi_eq
  intro s hs
  classical
  simp only [Measure.dirac_apply' _ (MeasurableSet.univ_pi hs),
    Measure.dirac_apply' _ (hs _), indicator_apply, Pi.one_apply, mem_univ_pi]
  by_cases h : ∀ r, k r ∈ s r
  · simp [h]
  · push Not at h
    obtain ⟨r, hr⟩ := h
    rw [ite_eq_right (by simpa using not_forall.mpr ⟨r, hr⟩)]
    exact (Finset.prod_eq_zero (Finset.mem_univ r) (ite_eq_right hr)).symm

/-- Separate the four side indices from their four position-depth pairs. -/
lemma lintegral_intensity_tuple (T : ℝ) (F : (Fin 4 → Pt m) → ℝ≥0∞)
    (hF : Measurable F) :
    (∫⁻ x, F x ∂(Measure.pi fun _ : Fin 4 => Λ K T)) =
      ∑ k : Fin 4 → Fin m, ∫⁻ p : Fin 4 → ℝ × ℝ,
        F (fun r => (k r, p r)) ∂(Measure.pi fun r =>
          volume.restrict (Icc (K.a (k r)) (K.b (k r)) ×ˢ Icc (0 : ℝ) T)) := by
  rw [intensity_pi_eq K T, lintegral_finsetSum_measure]
  apply Finset.sum_congr rfl
  intro k _
  let e := MeasurableEquiv.arrowProdEquivProdArrow (Fin m) (ℝ × ℝ) (Fin 4)
  have he := measurePreserving_arrowProdEquivProdArrow (Fin m) (ℝ × ℝ) (Fin 4)
    (fun r => Measure.dirac (k r))
    (fun r => volume.restrict (Icc (K.a (k r)) (K.b (k r)) ×ˢ Icc (0 : ℝ) T))
  change MeasurePreserving e _ _ at he
  have h := he.lintegral_comp_emb e.measurableEmbedding (fun q => F (e.symm q))
  simp only [e.symm_apply_apply] at h
  have hm : Measurable (fun q => F (e.symm q)) := hF.comp e.symm.measurable
  rw [h, pi_dirac_tuple, lintegral_prod _ hm.aemeasurable, lintegral_dirac']
  · rfl
  · exact hm.lintegral_prod_right'

def pointsOf (k : Fin 4 → Fin m) (s D : Fin 4 → ℝ) : Fin 4 → Pt m :=
  fun r => (k r, s r, D r)

lemma lintegral_intensity_positions (T : ℝ) (F : (Fin 4 → Pt m) → ℝ≥0∞)
    (hF : Measurable F) :
    (∫⁻ x, F x ∂(Measure.pi fun _ : Fin 4 => Λ K T)) =
      ∑ k : Fin 4 → Fin m, ∫⁻ s : Fin 4 → ℝ,
        ∫⁻ D : Fin 4 → ℝ, F (pointsOf k s D)
          ∂(Measure.pi fun _ : Fin 4 => volume.restrict (Icc (0 : ℝ) T))
        ∂(Measure.pi fun r => volume.restrict (Icc (K.a (k r)) (K.b (k r)))) := by
  rw [lintegral_intensity_tuple K T F hF]
  apply Finset.sum_congr rfl
  intro k _
  have hρ : ∀ r : Fin 4,
      volume.restrict (Icc (K.a (k r)) (K.b (k r)) ×ˢ Icc (0 : ℝ) T) =
        (volume.restrict (Icc (K.a (k r)) (K.b (k r)))).prod
          (volume.restrict (Icc (0 : ℝ) T)) := by
    intro r; rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
  simp_rw [hρ]
  let e := MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ (Fin 4)
  have he := measurePreserving_arrowProdEquivProdArrow ℝ ℝ (Fin 4)
    (fun r => volume.restrict (Icc (K.a (k r)) (K.b (k r))))
    (fun _ => volume.restrict (Icc (0 : ℝ) T))
  change MeasurePreserving e _ _ at he
  have hG : Measurable (fun p : Fin 4 → ℝ × ℝ => F (fun r => (k r, p r))) := by
    apply hF.comp
    exact Measurable.of_eval fun r => measurable_const.prodMk (measurable_pi_apply r)
  have h := he.lintegral_comp_emb e.measurableEmbedding
    (fun q => F (fun r => (k r, (e.symm q) r)))
  simp only [e.symm_apply_apply] at h
  have hm : Measurable (fun q => F (fun r => (k r, (e.symm q) r))) :=
    hG.comp e.symm.measurable
  rw [h, lintegral_prod _ hm.aemeasurable]
  rfl

noncomputable def vertexWeight (T : ℝ) (x : Fin 4 → Pt m) : ℝ≥0∞ :=
  {x | VertexGood K T x}.indicator
    (fun x => ENNReal.ofReal (Real.exp (2 * (vertexCopy K x).1))) x

lemma measurable_vertexWeight (T : ℝ) : Measurable (vertexWeight K T) :=
  (ENNReal.measurable_ofReal.comp (Real.continuous_exp.measurable.comp
    (measurable_const.mul (measurable_vertexCopy K).fst))).indicator
      (measurableSet_VertexGood K T)

def RowGood (k : Fin 4 → Fin m) (s : Fin 4 → ℝ) : Prop :=
  (vertexMatrix K (pointsOf k s 0)).det ≠ 0 ∧
    ∀ r, 0 < vertexCert K (pointsOf k s 0) r

noncomputable def rowDensity (k : Fin 4 → Fin m) (s : Fin 4 → ℝ) : ℝ≥0∞ :=
  {s | RowGood K k s}.indicator
    (fun s => ENNReal.ofReal |(vertexMatrix K (pointsOf k s 0)).det|) s

lemma points_matrix (k : Fin 4 → Fin m) (s D : Fin 4 → ℝ) :
    vertexMatrix K (pointsOf k s D) = vertexMatrix K (pointsOf k s 0) := rfl

lemma points_cert (k : Fin 4 → Fin m) (s D : Fin 4 → ℝ) :
    vertexCert K (pointsOf k s D) = vertexCert K (pointsOf k s 0) := rfl

lemma vertexWeight_depth (T : ℝ) (k : Fin 4 → Fin m) (s D : Fin 4 → ℝ)
    (h : RowGood K k s) :
    vertexWeight K T (pointsOf k s D) =
      fitWeightBelow K T ((vertexMatrix K (pointsOf k s 0))⁻¹ *ᵥ (-D)) := by
  let v := (vertexMatrix K (pointsOf k s 0))⁻¹ *ᵥ (-D)
  have hz : vertexCopy K (pointsOf k s D) = copyOfVec v := rfl
  by_cases hg : VertexGood K T (pointsOf k s D)
  · have hF : v ∈ {z | Fits K (copyOfVec z)} := by
      change Fits K (copyOfVec v); rw [← hz]; exact hg.2.2.1
    have hB : v ∈ {z | Below K T (copyOfVec z)} := by
      change Below K T (copyOfVec v); rw [← hz]; exact hg.2.2.2
    rw [vertexWeight, indicator_of_mem
      (show pointsOf k s D ∈ {x | VertexGood K T x} from hg),
      fitWeightBelow, indicator_of_mem hB, fitWeight, indicator_of_mem hF]
    rfl
  · rw [vertexWeight, indicator_of_notMem
      (show pointsOf k s D ∉ {x | VertexGood K T x} from hg)]
    by_cases hb : v ∈ {z | Below K T (copyOfVec z)}
    · have hf : v ∉ {z | Fits K (copyOfVec z)} := by
        intro hf
        apply hg
        exact ⟨h.1, h.2, hz.symm ▸ hf, hz.symm ▸ hb⟩
      rw [fitWeightBelow, indicator_of_mem hb, fitWeight, indicator_of_notMem hf]
    · rw [fitWeightBelow, indicator_of_notMem hb]

lemma vertexWeight_zero_of_not_rowGood (T : ℝ) (k : Fin 4 → Fin m) (s D : Fin 4 → ℝ)
    (h : ¬ RowGood K k s) : vertexWeight K T (pointsOf k s D) = 0 := by
  apply indicator_of_notMem
  intro hx
  exact h ⟨hx.1, hx.2.1⟩

lemma vertexGood_depths (T : ℝ) (k : Fin 4 → Fin m) (s D : Fin 4 → ℝ)
    (hs : ∀ r, s r ∈ Icc (K.a (k r)) (K.b (k r)))
    (h : VertexGood K T (pointsOf k s D)) : ∀ r, D r ∈ Icc (0 : ℝ) T := by
  intro r
  have ht := vertexCopy_tight K _ h.1 r
  have he : D r = (vertexCopy K (pointsOf k s D)).2.2 * s r -
      Hs K (vertexCopy K (pointsOf k s D)) (k r) := by
    unfold gx at ht
    change Hs K (vertexCopy K (pointsOf k s D)) (k r) -
      (vertexCopy K (pointsOf k s D)).2.2 * s r + D r = 0 at ht
    linarith
  rw [he]
  exact ⟨line_nonneg (h.2.2.1 (k r)) (hs r), below_line K T _ h.2.2.2 (k r) (hs r)⟩

/-- The cutoff on the four depths is redundant once the fitting lines are below `T`. -/
lemma vertex_depth_integral (T : ℝ) (k : Fin 4 → Fin m) (s : Fin 4 → ℝ)
    (hs : ∀ r, s r ∈ Icc (K.a (k r)) (K.b (k r))) :
    (∫⁻ D, vertexWeight K T (pointsOf k s D)
      ∂(Measure.pi fun _ : Fin 4 => volume.restrict (Icc (0 : ℝ) T))) =
        rowDensity K k s * ∫⁻ z, fitWeightBelow K T z := by
  have hrestrict : (∫⁻ D, vertexWeight K T (pointsOf k s D)
      ∂(Measure.pi fun _ : Fin 4 => volume.restrict (Icc (0 : ℝ) T))) =
        ∫⁻ D, vertexWeight K T (pointsOf k s D) := by
    rw [← Measure.restrict_pi_pi (fun _ : Fin 4 => (volume : Measure ℝ))
      (fun _ => Icc (0 : ℝ) T)]
    change (∫⁻ D in univ.pi (fun _ : Fin 4 => Icc (0 : ℝ) T),
      vertexWeight K T (pointsOf k s D)) = _
    rw [← lintegral_indicator (MeasurableSet.univ_pi fun _ => measurableSet_Icc)]
    apply lintegral_congr
    intro D
    by_cases hD : D ∈ univ.pi (fun _ : Fin 4 => Icc (0 : ℝ) T)
    · exact indicator_of_mem (f := fun D => vertexWeight K T (pointsOf k s D)) hD
    · rw [indicator_of_notMem hD]
      symm
      apply indicator_of_notMem
      intro hx
      exact hD (mem_univ_pi.mpr (vertexGood_depths K T k s D hs hx))
  rw [hrestrict]
  by_cases h : RowGood K k s
  · simp_rw [vertexWeight_depth K T k s _ h]
    rw [lintegral_depths _ h.1 _ (measurable_fitWeightBelow K T)]
    rw [rowDensity, indicator_of_mem (show s ∈ {s | RowGood K k s} from h)]
  · simp_rw [vertexWeight_zero_of_not_rowGood K T k s _ h]
    rw [lintegral_zero, rowDensity, indicator_of_notMem (show s ∉ {s | RowGood K k s} from h),
      zero_mul]

lemma measurable_pointsOf_zero (k : Fin 4 → Fin m) :
    Measurable (fun s : Fin 4 → ℝ => pointsOf k s 0) :=
  Measurable.of_eval fun r =>
    measurable_const.prodMk ((measurable_pi_apply r).prodMk measurable_const)

lemma measurableSet_RowGood (k : Fin 4 → Fin m) : MeasurableSet {s | RowGood K k s} := by
  have hM := (measurable_vertexMatrix K).comp (measurable_pointsOf_zero k)
  have hC := (measurable_vertexCert K).comp (measurable_pointsOf_zero k)
  have hp : MeasurableSet {s | ∀ r, 0 < vertexCert K (pointsOf k s 0) r} := by
    simp only [ofPred_forall]
    exact MeasurableSet.iInter fun r => measurableSet_lt measurable_const
      ((measurable_pi_apply r).comp hC)
  exact (measurableSet_eq_fun (continuous_id.matrix_det.measurable.comp hM)
    measurable_const).compl.inter hp

lemma measurable_rowDensity (k : Fin 4 → Fin m) : Measurable (rowDensity K k) := by
  have hM := (measurable_vertexMatrix K).comp (measurable_pointsOf_zero k)
  exact (ENNReal.measurable_ofReal.comp
    (continuous_abs.measurable.comp (continuous_id.matrix_det.measurable.comp hM))).indicator
      (measurableSet_RowGood K k)

lemma positions_ae (k : Fin 4 → Fin m) :
    ∀ᵐ s : Fin 4 → ℝ
      ∂(Measure.pi fun r => volume.restrict (Icc (K.a (k r)) (K.b (k r)))),
      ∀ r, s r ∈ Icc (K.a (k r)) (K.b (k r)) := by
  rw [← Measure.restrict_pi_pi (fun _ : Fin 4 => (volume : Measure ℝ))]
  exact (ae_restrict_mem (MeasurableSet.univ_pi fun _ => measurableSet_Icc)).mono
    fun _ hs => mem_univ_pi.mp hs

/-- The four-point density, including the factor `1/4!` for unordered tight sets. -/
noncomputable def vertexDensity : ℝ≥0∞ :=
  (1 / 24) * ∑ k : Fin 4 → Fin m, ∫⁻ s, rowDensity K k s
    ∂(Measure.pi fun r => volume.restrict (Icc (K.a (k r)) (K.b (k r))))

/-- The complete finite-cutoff vertex count: Mecke, strip coordinates and the Jacobian.
The spatial factor is independent of the selected sides and positions. -/
theorem vertex_count_factor (T : ℝ) :
    (1 / 24) * vertexOrderedCount K T =
      vertexDensity K * ∫⁻ z, fitWeightBelow K T z := by
  have hc : vertexOrderedCount K T =
      (∑ k : Fin 4 → Fin m, ∫⁻ s, rowDensity K k s
        ∂(Measure.pi fun r => volume.restrict (Icc (K.a (k r)) (K.b (k r))))) *
          ∫⁻ z, fitWeightBelow K T z := by
    rw [vertex_mecke]
    change (∫⁻ x, vertexWeight K T x ∂(Measure.pi fun _ : Fin 4 => Λ K T)) = _
    rw [lintegral_intensity_positions K T _ (measurable_vertexWeight K T), Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k _
    calc (∫⁻ s, ∫⁻ D, vertexWeight K T (pointsOf k s D)
        ∂(Measure.pi fun _ : Fin 4 => volume.restrict (Icc (0 : ℝ) T))
        ∂(Measure.pi fun r => volume.restrict (Icc (K.a (k r)) (K.b (k r)))))
        = ∫⁻ s, rowDensity K k s * (∫⁻ z, fitWeightBelow K T z)
          ∂(Measure.pi fun r => volume.restrict (Icc (K.a (k r)) (K.b (k r)))) := by
            apply lintegral_congr_ae
            filter_upwards [positions_ae K k] with s hs
            exact vertex_depth_integral K T k s hs
      _ = _ := lintegral_mul_const _ (measurable_rowDensity K k)
  rw [hc, vertexDensity, mul_assoc]

lemma fitWeightBelow_iSup (z : Fin 4 → ℝ) :
    (⨆ n : ℕ, fitWeightBelow K n z) = fitWeight K z := by
  apply le_antisymm
  · apply iSup_le
    intro n
    exact Set.indicator_le_self (s := {z | Below K n (copyOfVec z)}) (f := fitWeight K) z
  · obtain ⟨n, hn⟩ := exists_below K (copyOfVec z)
    calc fitWeight K z = fitWeightBelow K n z :=
      (indicator_of_mem (f := fitWeight K) (show z ∈ {z | Below K n (copyOfVec z)} from hn)).symm
    _ ≤ _ := le_iSup (fun n : ℕ => fitWeightBelow K n z) n

/-- Letting the cutoff tend to infinity in the actual Poisson vertex candidate count.
This does not assume the optimum classification or finite-sample convergence. -/
theorem vertex_count_limit :
    Filter.Tendsto (fun n : ℕ => (1 / 24) * vertexOrderedCount K n) Filter.atTop
      (nhds (vertexDensity K * ∫⁻ z, fitWeight K z)) := by
  simp_rw [vertex_count_factor]
  have hmono : Monotone (fun n : ℕ => vertexDensity K * ∫⁻ z, fitWeightBelow K n z) := by
    intro n q hnq
    exact mul_le_mul le_rfl (lintegral_mono fun z => fitWeightBelow_mono K z hnq) bot_le bot_le
  have hs : (⨆ n : ℕ, vertexDensity K * ∫⁻ z, fitWeightBelow K n z) =
      vertexDensity K * ∫⁻ z, fitWeight K z := by
    rw [← ENNReal.mul_iSup, ← lintegral_iSup (fun n => measurable_fitWeightBelow K n)]
    · simp only [fitWeightBelow_iSup]
    · intro n q hnq z
      exact fitWeightBelow_mono K z hnq
  rw [← hs]
  exact tendsto_atTop_iSup hmono

end Enclosing
