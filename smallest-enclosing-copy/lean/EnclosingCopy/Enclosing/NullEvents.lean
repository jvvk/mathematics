import EnclosingCopy.Enclosing.VertexCount
import EnclosingCopy.Poisson.Law

/-!
# No extra tight point at a copy determined by other sampled points

The depth coordinate has a continuous law. For any measurable rule determining
a copy from `k` points, an additional distinct Poisson point is almost surely
not tight at that copy. The statement is proved with Mecke, not by asserting
independence after selecting the optimum.
-/

namespace Enclosing
open MeasureTheory Set ENNReal
variable {m : ℕ} (K : Sides m)

lemma measurable_gx_joint : Measurable (fun q : Copy × Pt m => gx K q.1 q.2) := by
  have hH : Measurable (fun q : Copy × Pt m => Hs K q.1 q.2.1) := by
    unfold Hs dot
    have hh : Measurable (fun q : Copy × Pt m => K.h q.2.1) :=
      (measurable_of_countable K.h).comp (measurable_fst.comp measurable_snd)
    have hu1 : Measurable (fun q : Copy × Pt m => (K.u q.2.1).1) :=
      (measurable_of_countable fun i => (K.u i).1).comp
      (measurable_fst.comp measurable_snd)
    have hu2 : Measurable (fun q : Copy × Pt m => (K.u q.2.1).2) :=
      (measurable_of_countable fun i => (K.u i).2).comp
      (measurable_fst.comp measurable_snd)
    exact (measurable_fst.fst.mul hh).add
      ((measurable_fst.snd.fst.fst.mul hu1).add (measurable_fst.snd.fst.snd.mul hu2))
  exact (hH.sub (measurable_fst.snd.snd.mul measurable_snd.snd.fst)).add
    measurable_snd.snd.snd

lemma measurableSet_tight (z : Copy) : MeasurableSet {x | gx K z x = 0} :=
  measurableSet_eq_fun ((measurable_gx_joint K).comp (measurable_const.prodMk measurable_id))
    measurable_const

/-- A fixed copy has intensity zero on its tight lines. -/
theorem intensity_tight_zero (T : ℝ) (z : Copy) : Λ K T {x | gx K z x = 0} = 0 := by
  unfold Λ
  rw [Measure.coe_finsetSum, Finset.sum_apply]
  apply Finset.sum_eq_zero
  intro i _
  rw [Measure.dirac_prod, Measure.map_apply measurable_prodMk_left (measurableSet_tight K z)]
  apply le_antisymm _ bot_le
  calc (volume.restrict (Icc (K.a i) (K.b i) ×ˢ Icc (0 : ℝ) T))
        (Prod.mk i ⁻¹' {x | gx K z x = 0})
      ≤ volume (Prod.mk i ⁻¹' {x | gx K z x = 0}) := Measure.restrict_apply_le _ _
    _ = 0 := by
      rw [Measure.volume_eq_prod,
        Measure.prod_apply ((measurableSet_tight K z).preimage measurable_prodMk_left)]
      have hs : ∀ s : ℝ, Prod.mk s ⁻¹' (Prod.mk i ⁻¹' {x | gx K z x = 0}) =
          {z.2.2 * s - Hs K z i} := by
        intro s
        ext D
        simp only [mem_preimage, mem_ofPred_eq, mem_singleton_iff, gx]
        constructor <;> intro h <;> linarith
      simp_rw [hs, measure_singleton]
      exact lintegral_zero

variable {k : ℕ} (c : (Fin k → Pt m) → Copy) (hc : Measurable c)

def extraTight (x : Fin (k + 1) → Pt m) : Prop :=
  gx K (c (fun r => x (Fin.last k |>.succAbove r))) (x (Fin.last k)) = 0

include hc

lemma measurableSet_extraTight : MeasurableSet {x | extraTight K c x} := by
  have hfirst : Measurable (fun x : Fin (k + 1) → Pt m =>
      fun r => x (Fin.last k |>.succAbove r)) :=
    Measurable.of_eval fun r => measurable_pi_apply _
  exact measurableSet_eq_fun ((measurable_gx_joint K).comp
    ((hc.comp hfirst).prodMk (measurable_pi_apply (Fin.last k)))) measurable_const

/-- The Mecke integrand for an extra tight point is null. -/
theorem extraTight_integral_zero (T : ℝ) :
    (∫⁻ x : Fin (k + 1) → Pt m,
      {x | extraTight K c x}.indicator (1 : (Fin (k + 1) → Pt m) → ℝ≥0∞) x
        ∂(Measure.pi fun _ => Λ K T)) = 0 := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k + 1) => Pt m) (Fin.last k)
  have he := measurePreserving_piFinSuccAbove (fun _ : Fin (k + 1) => Λ K T) (Fin.last k)
  change MeasurePreserving e _ _ at he
  let F : (Fin (k + 1) → Pt m) → ℝ≥0∞ := {x | extraTight K c x}.indicator 1
  have h := he.lintegral_comp_emb e.measurableEmbedding (fun q => F (e.symm q))
  simp only [e.symm_apply_apply] at h
  rw [h]
  have hM : Measurable (fun q => F (e.symm q)) :=
    (measurable_one.indicator (measurableSet_extraTight K c hc)).comp e.symm.measurable
  rw [lintegral_prod_symm _ hM.aemeasurable]
  have inner : ∀ x : Fin k → Pt m, (∫⁻ p, F (e.symm (p, x)) ∂Λ K T) = 0 := by
    intro x
    have hf : (fun p : Pt m => F (e.symm (p, x))) =
        {p | gx K (c x) p = 0}.indicator 1 := by
      funext p
      have he1 : e (e.symm (p, x)) = (p, x) := e.apply_symm_apply _
      have hi : (e.symm (p, x)) (Fin.last k) = p := congrArg Prod.fst he1
      have hx : (fun r => (e.symm (p, x)) ((Fin.last k).succAbove r)) = x :=
        congrArg Prod.snd he1
      simp only [F, Set.indicator, mem_ofPred_eq, extraTight, hi, hx, Pi.one_apply]
    rw [hf, lintegral_indicator_one (measurableSet_tight K (c x)),
      intensity_tight_zero K T (c x)]
  simp_rw [inner]
  exact lintegral_zero

/-- The expected number of ordered distinct tuples with an extra tight point is zero. -/
theorem extraTight_count_zero (T : ℝ) :
    (∑' n : ℕ, PoissonPP.w0 (Λ K T) / n.factorial *
      ∫⁻ y : Fin n → Pt m, ∑ i : Fin (k + 1) ↪ Fin n,
        {x | extraTight K c x}.indicator (1 : (Fin (k + 1) → Pt m) → ℝ≥0∞) (y ∘ i)
        ∂(Measure.pi fun _ => Λ K T)) = 0 := by
  have h := PoissonPP.mecke (Λ K T) (k + 1)
    (fun x _ => {x | extraTight K c x}.indicator 1 x)
    (fun _ => (measurable_one.indicator (measurableSet_extraTight K c hc)).comp measurable_fst)
  rw [h]
  simp only [PoissonPP.expect_const]
  exact extraTight_integral_zero K c hc T

/-- An extra tight point among distinct points of the labelled Poisson sample. -/
def BadExtra (ω : PoissonPP.Sample (Pt m)) : Prop :=
  ∃ i : Fin (k + 1) ↪ Fin ω.1, extraTight K c (ω.2 ∘ i)

lemma measurableSet_BadExtra : MeasurableSet {ω | BadExtra K c ω} := by
  apply PoissonPP.measurableSet_sample
  intro n
  change MeasurableSet {y : Fin n → Pt m | ∃ i : Fin (k + 1) ↪ Fin n,
    extraTight K c (y ∘ i)}
  simp only [ofPred_exists]
  apply MeasurableSet.iUnion
  intro i
  exact (measurableSet_extraTight K c hc).preimage
    (Measurable.of_eval fun r => measurable_pi_apply (i r))

/-- No unproved genericity assumption: the bad event has probability zero. -/
theorem badExtra_prob_zero (T : ℝ) :
    PoissonPP.law (Λ K T) {ω | BadExtra K c ω} = 0 := by
  have hbad := measurableSet_BadExtra K c hc
  rw [← lintegral_indicator_one hbad,
    PoissonPP.lintegral_law _ _ (measurable_one.indicator hbad)]
  apply le_antisymm _ bot_le
  change _ ≤ (0 : ℝ≥0∞)
  rw [← extraTight_count_zero K c hc T]
  apply ENNReal.tsum_le_tsum
  intro n
  apply mul_le_mul le_rfl _ bot_le bot_le
  apply lintegral_mono
  intro y
  change {ω | BadExtra K c ω}.indicator
    (1 : PoissonPP.Sample (Pt m) → ℝ≥0∞) ⟨n, y⟩ ≤
      ∑ i : Fin (k + 1) ↪ Fin n,
        {x | extraTight K c x}.indicator (1 : (Fin (k + 1) → Pt m) → ℝ≥0∞) (y ∘ i)
  by_cases hy : BadExtra K c ⟨n, y⟩
  · rw [indicator_of_mem (show (⟨n, y⟩ : PoissonPP.Sample (Pt m)) ∈
      {ω | BadExtra K c ω} from hy), Pi.one_apply]
    obtain ⟨i, hi⟩ := hy
    have hsum := Finset.single_le_sum
      (s := Finset.univ) (f := fun j : Fin (k + 1) ↪ Fin n =>
        {x | extraTight K c x}.indicator (1 : (Fin (k + 1) → Pt m) → ℝ≥0∞) (y ∘ j))
      (fun _ _ => bot_le) (Finset.mem_univ i)
    rw [indicator_of_mem (show y ∘ i ∈ {x | extraTight K c x} from hi),
      Pi.one_apply] at hsum
    exact hsum
  · rw [indicator_of_notMem (show (⟨n, y⟩ : PoissonPP.Sample (Pt m)) ∉
      {ω | BadExtra K c ω} from hy)]
    exact bot_le

omit hc in
/-- Specialisation to the copy determined by four tight points. -/
theorem no_extra_tight_vertex (T : ℝ) :
    PoissonPP.law (Λ K T) {ω | BadExtra K (vertexCopy K) ω} = 0 :=
  badExtra_prob_zero K (vertexCopy K) (measurable_vertexCopy K) T

end Enclosing
