import EnclosingCopy.Enclosing.NullEvents
import Mathlib.Data.Fintype.Perm

/-!
# Vertex-candidate probabilities

The Mecke count in `VertexCount` is converted here into the probability of a
measurable event on the actual finite Poisson sample space. Positive certificates
give uniqueness of the optimum. The extra-tight-point null theorem then ensures
that all candidate tuples select the same four sampled indices, so there are
exactly `4! = 24` orderings whenever a candidate exists.

`vertex_candidate_prob_factor` and `vertex_candidate_prob_limit` are probability
theorems. They concern the certified vertex-candidate event; they do not assert
the full vertex/segment classification or convergence of the original iid model.
-/

namespace Enclosing
open MeasureTheory Set Matrix ENNReal
open scoped Classical
variable {m : ℕ} (K : Sides m)

lemma vertexCopy_eq_of_tight (x : Fin 4 → Pt m)
    (hA : (vertexMatrix K x).det ≠ 0) (z : Copy)
    (ht : ∀ r, gx K z (x r) = 0) : vertexCopy K x = z := by
  have hz : vertexMatrix K x *ᵥ zvec z = fun r => -(x r).2.2 := by
    ext r
    have h := ht r
    rw [gx_eq] at h
    change (vertexMatrix K x *ᵥ zvec z) r + (x r).2.2 = 0 at h
    linarith
  have h := Matrix.nonsing_inv_mul (vertexMatrix K x) (isUnit_iff_ne_zero.mpr hA)
  unfold vertexCopy
  rw [← hz, Matrix.mulVec_mulVec, h, Matrix.one_mulVec, copyOfVec_zvec]

lemma vertexCert_eq_of_certificate (x : Fin 4 → Pt m)
    (hA : (vertexMatrix K x).det ≠ 0) (l : Fin 4 → ℝ)
    (hl : ∀ c, ∑ r, l r * row K (x r) c = if c = 0 then 1 else 0) :
    vertexCert K x = l := by
  have he : l ᵥ* vertexMatrix K x = Pi.single 0 1 := by
    ext c
    simpa [Matrix.vecMul, dotProduct, vertexMatrix, Pi.single_apply, eq_comm] using hl c
  have h := Matrix.mul_nonsing_inv (vertexMatrix K x) (isUnit_iff_ne_zero.mpr hA)
  unfold vertexCert
  rw [← he, Matrix.vecMul_vecMul, h, Matrix.vecMul_one]

lemma vertexMatrix_perm (x : Fin 4 → Pt m) (e : Equiv.Perm (Fin 4)) :
    vertexMatrix K (x ∘ e) = (vertexMatrix K x).submatrix e id := rfl

lemma vertexMatrix_perm_nonsingular (x : Fin 4 → Pt m) (e : Equiv.Perm (Fin 4))
    (hA : (vertexMatrix K x).det ≠ 0) : (vertexMatrix K (x ∘ e)).det ≠ 0 := by
  rw [vertexMatrix_perm, Matrix.det_permute]
  exact mul_ne_zero (by simp) hA

lemma vertexCopy_perm (x : Fin 4 → Pt m) (e : Equiv.Perm (Fin 4))
    (hA : (vertexMatrix K x).det ≠ 0) : vertexCopy K (x ∘ e) = vertexCopy K x :=
  vertexCopy_eq_of_tight K _ (vertexMatrix_perm_nonsingular K x e hA) _
    (fun r => vertexCopy_tight K x hA (e r))

lemma vertexCert_perm (x : Fin 4 → Pt m) (e : Equiv.Perm (Fin 4))
    (hA : (vertexMatrix K x).det ≠ 0) : vertexCert K (x ∘ e) = vertexCert K x ∘ e := by
  apply vertexCert_eq_of_certificate K _ (vertexMatrix_perm_nonsingular K x e hA)
  intro c
  change (∑ r, vertexCert K x (e r) * row K (x (e r)) c) = _
  rw [Equiv.sum_comp e (fun r => vertexCert K x r * row K (x r) c)]
  exact vertexCert_eq K x hA c

lemma vertexGood_perm (T : ℝ) (x : Fin 4 → Pt m) (e : Equiv.Perm (Fin 4))
    (hx : VertexGood K T x) : VertexGood K T (x ∘ e) := by
  refine ⟨vertexMatrix_perm_nonsingular K x e hx.1, ?_, ?_, ?_⟩
  · rw [vertexCert_perm K x e hx.1]
    exact fun r => hx.2.1 (e r)
  · rw [vertexCopy_perm K x e hx.1]; exact hx.2.2.1
  · rw [vertexCopy_perm K x e hx.1]; exact hx.2.2.2

def VertexCandidate {n : ℕ} (T : ℝ) (y : Fin n → Pt m) (i : Fin 4 ↪ Fin n) : Prop :=
  VertexGood K T (y ∘ i) ∧ Feasible K (PoissonPP.config y) (vertexCopy K (y ∘ i))

lemma feasible_config_iff {n : ℕ} (y : Fin n → Pt m) (z : Copy) :
    Feasible K (PoissonPP.config y) z ↔ ∀ t, 0 ≤ gx K z (y t) := by
  simp only [Feasible, PoissonPP.mem_config, gx_nonneg_iff]
  constructor
  · intro h t; exact h _ ⟨t, rfl⟩
  · intro h p ⟨t, ht⟩; rw [← ht]; exact h t

lemma vertexCandidates_same_copy {n : ℕ} (T : ℝ) (y : Fin n → Pt m)
    (i j : Fin 4 ↪ Fin n) (hi : VertexCandidate K T y i)
    (hj : VertexCandidate K T y j) : vertexCopy K (y ∘ i) = vertexCopy K (y ∘ j) := by
  have hiy := (feasible_config_iff K y _).mp hi.2
  have hjy := (feasible_config_iff K y _).mp hj.2
  have hi_le := vertexGood_optimal K T _ hi.1 _ (fun r => hjy (i r))
  have hj_le := vertexGood_optimal K T _ hj.1 _ (fun r => hiy (j r))
  exact vertexGood_unique K T _ hj.1 _ (fun r => hiy (j r)) (le_antisymm hi_le hj_le)

def appendEmbedding {n : ℕ} (i : Fin 4 ↪ Fin n) (t : Fin n)
    (ht : t ∉ Set.range i) : Fin 5 ↪ Fin n where
  toFun := Fin.lastCases t i
  inj' := by
    intro a b h
    cases a using Fin.lastCases <;> cases b using Fin.lastCases
    · rfl
    · simp at h
      exact False.elim (ht ⟨_, h.symm⟩)
    · simp at h
      exact False.elim (ht ⟨_, h⟩)
    · simp at h
      exact congrArg Fin.castSucc h

lemma tight_index_in_range {n : ℕ} (y : Fin n → Pt m)
    (hbad : ¬ BadExtra K (vertexCopy K) ⟨n, y⟩) (i : Fin 4 ↪ Fin n) (t : Fin n)
    (ht : gx K (vertexCopy K (y ∘ i)) (y t) = 0) : t ∈ Set.range i := by
  by_contra h
  apply hbad
  refine ⟨appendEmbedding i t h, ?_⟩
  have hl : appendEmbedding i t h (Fin.last 4) = t := by
    change Fin.lastCases t (fun r => i r) (Fin.last 4) = t
    simp only [Fin.lastCases_last]
  have hf : (fun r : Fin 4 => (y ∘ appendEmbedding i t h) ((Fin.last 4).succAbove r)) =
      y ∘ i := by
    funext r
    change y (Fin.lastCases t i ((Fin.last 4).succAbove r)) = y (i r)
    rw [Fin.succAbove_last, Fin.lastCases_castSucc]
  change gx K (vertexCopy K _) ((y ∘ appendEmbedding i t h) (Fin.last 4)) = 0
  rw [hf]
  change gx K (vertexCopy K (y ∘ i)) (y (appendEmbedding i t h (Fin.last 4))) = 0
  rw [hl]
  exact ht

lemma vertexCandidates_range_eq {n : ℕ} (T : ℝ) (y : Fin n → Pt m)
    (hbad : ¬ BadExtra K (vertexCopy K) ⟨n, y⟩)
    (i j : Fin 4 ↪ Fin n) (hi : VertexCandidate K T y i)
    (hj : VertexCandidate K T y j) : Set.range i = Set.range j := by
  have he := vertexCandidates_same_copy K T y i j hi hj
  apply Set.Subset.antisymm
  · rintro t ⟨r, rfl⟩
    apply tight_index_in_range K y hbad j
    rw [← he]
    exact vertexCopy_tight K _ hi.1.1 r
  · rintro t ⟨r, rfl⟩
    apply tight_index_in_range K y hbad i
    rw [he]
    exact vertexCopy_tight K _ hj.1.1 r

lemma vertexCandidate_perm {n : ℕ} (T : ℝ) (y : Fin n → Pt m)
    (i : Fin 4 ↪ Fin n) (e : Equiv.Perm (Fin 4))
    (hi : VertexCandidate K T y i) : VertexCandidate K T y (e.toEmbedding.trans i) := by
  have he : y ∘ (e.toEmbedding.trans i) = (y ∘ i) ∘ e := rfl
  change VertexGood K T (y ∘ (e.toEmbedding.trans i)) ∧ _
  rw [he, vertexCopy_perm K _ e hi.1.1]
  exact ⟨vertexGood_perm K T _ e hi.1, hi.2⟩

lemma embedding_eq_perm {n : ℕ} (i j : Fin 4 ↪ Fin n)
    (h : Set.range j ⊆ Set.range i) : ∃ e : Equiv.Perm (Fin 4), j = e.toEmbedding.trans i := by
  classical
  have hr : ∀ r, ∃ s, i s = j r := fun r => h ⟨r, rfl⟩
  choose f hf using hr
  have hf_inj : Function.Injective f := by
    intro r s hrs
    apply j.injective
    rw [← hf r, ← hf s, hrs]
  let e : Equiv.Perm (Fin 4) := Equiv.ofBijective f
    ⟨hf_inj, Finite.surjective_of_injective hf_inj⟩
  refine ⟨e, ?_⟩
  apply Function.Embedding.ext
  intro r
  exact (hf r).symm

lemma vertexCandidate_card {n : ℕ} (T : ℝ) (y : Fin n → Pt m)
    (hbad : ¬ BadExtra K (vertexCopy K) ⟨n, y⟩)
    (i : Fin 4 ↪ Fin n) (hi : VertexCandidate K T y i) :
    Fintype.card {j : Fin 4 ↪ Fin n // VertexCandidate K T y j} = 24 := by
  classical
  let f : Equiv.Perm (Fin 4) → {j : Fin 4 ↪ Fin n // VertexCandidate K T y j} :=
    fun e => ⟨e.toEmbedding.trans i, vertexCandidate_perm K T y i e hi⟩
  have hf : Function.Bijective f := by
    constructor
    · intro e e' he
      apply Equiv.ext
      intro r
      apply i.injective
      exact congrArg (fun j : {j : Fin 4 ↪ Fin n // VertexCandidate K T y j} => j.val r) he
    · rintro ⟨j, hj⟩
      obtain ⟨e, he⟩ := embedding_eq_perm i j
        (by rw [vertexCandidates_range_eq K T y hbad i j hi hj])
      refine ⟨e, ?_⟩
      apply Subtype.ext
      exact he.symm
  have hcard := Fintype.card_congr (Equiv.ofBijective f hf)
  rw [← hcard, Fintype.card_perm, Fintype.card_fin]
  norm_num

def HasVertexCandidate (T : ℝ) (ω : PoissonPP.Sample (Pt m)) : Prop :=
  ∃ i : Fin 4 ↪ Fin ω.1, VertexCandidate K T ω.2 i

noncomputable def sampleVertexCount (T : ℝ) (ω : PoissonPP.Sample (Pt m)) : ℝ≥0∞ :=
  ∑ i : Fin 4 ↪ Fin ω.1,
    {y | VertexCandidate K T y i}.indicator (1 : (Fin ω.1 → Pt m) → ℝ≥0∞) ω.2

lemma sampleVertexCount_eq (T : ℝ) (ω : PoissonPP.Sample (Pt m))
    (hbad : ¬ BadExtra K (vertexCopy K) ω) :
    sampleVertexCount K T ω =
      24 * {ω | HasVertexCandidate K T ω}.indicator 1 ω := by
  classical
  rcases ω with ⟨n, y⟩
  have hc : sampleVertexCount K T ⟨n, y⟩ =
      (Fintype.card {i : Fin 4 ↪ Fin n // VertexCandidate K T y i} : ℝ≥0∞) := by
    simp only [sampleVertexCount, Set.indicator, mem_ofPred_eq, Pi.one_apply]
    rw [Finset.sum_boole]
    congr 1
    simp [Fintype.card_subtype]
  by_cases hy : HasVertexCandidate K T ⟨n, y⟩
  · obtain ⟨i, hi⟩ := hy
    rw [hc, vertexCandidate_card K T y hbad i hi,
      indicator_of_mem (show (⟨n, y⟩ : PoissonPP.Sample (Pt m)) ∈
        {ω | HasVertexCandidate K T ω} from ⟨i, hi⟩), Pi.one_apply, mul_one]
    norm_num
  · have hn : IsEmpty {i : Fin 4 ↪ Fin n // VertexCandidate K T y i} :=
      ⟨fun i => hy ⟨i.val, i.property⟩⟩
    let := hn
    rw [hc, Fintype.card_of_isEmpty,
      indicator_of_notMem (show (⟨n, y⟩ : PoissonPP.Sample (Pt m)) ∉
        {ω | HasVertexCandidate K T ω} from hy), mul_zero]
    simp

lemma measurableSet_VertexCandidate {n : ℕ} (T : ℝ) (i : Fin 4 ↪ Fin n) :
    MeasurableSet {y : Fin n → Pt m | VertexCandidate K T y i} := by
  have hs : Measurable (fun y : Fin n → Pt m => y ∘ i) :=
    Measurable.of_eval fun r => measurable_pi_apply (i r)
  have hz := (measurable_vertexCopy K).comp hs
  have hf : MeasurableSet {y : Fin n → Pt m |
      Feasible K (PoissonPP.config y) (vertexCopy K (y ∘ i))} := by
    simp_rw [feasible_config_iff, ofPred_forall]
    apply MeasurableSet.iInter
    intro t
    exact measurableSet_le measurable_const
      ((measurable_gx_joint K).comp (hz.prodMk (measurable_pi_apply t)))
  exact ((measurableSet_VertexGood K T).preimage hs).inter hf

lemma measurableSet_HasVertexCandidate (T : ℝ) :
    MeasurableSet {ω | HasVertexCandidate K T ω} := by
  apply PoissonPP.measurableSet_sample
  intro n
  change MeasurableSet {y : Fin n → Pt m | ∃ i : Fin 4 ↪ Fin n, VertexCandidate K T y i}
  simp only [ofPred_exists]
  exact MeasurableSet.iUnion fun i => measurableSet_VertexCandidate K T i

lemma measurable_sampleVertexCount (T : ℝ) : Measurable (sampleVertexCount K T) := by
  intro s hs
  apply PoissonPP.measurableSet_sample
  intro n
  exact (Finset.measurable_sum (s := Finset.univ) fun i _ =>
    measurable_one.indicator (measurableSet_VertexCandidate K T i)) hs

lemma mem_rest_iff {n : ℕ} (y : Fin n → Pt m) (i : Fin 4 ↪ Fin n) (p : Pt m) :
    p ∈ PoissonPP.rest y i ↔ ∃ t, t ∉ Set.range i ∧ y t = p := by
  simp [PoissonPP.rest]

lemma vertex_feasible_rest_iff {n : ℕ} (y : Fin n → Pt m) (i : Fin 4 ↪ Fin n)
    (hA : (vertexMatrix K (y ∘ i)).det ≠ 0) :
    Feasible K (PoissonPP.rest y i) (vertexCopy K (y ∘ i)) ↔
      Feasible K (PoissonPP.config y) (vertexCopy K (y ∘ i)) := by
  rw [feasible_config_iff]
  constructor
  · intro h t
    by_cases ht : t ∈ Set.range i
    · obtain ⟨r, rfl⟩ := ht
      exact (vertexCopy_tight K _ hA r).ge
    · exact (gx_nonneg_iff K _ _).mpr (h _ ((mem_rest_iff y i _).mpr ⟨t, ht, rfl⟩))
  · intro h p hp
    obtain ⟨t, _, rfl⟩ := (mem_rest_iff y i p).mp hp
    exact (gx_nonneg_iff K _ _).mp (h t)

lemma candidate_indicator {n : ℕ} (T : ℝ) (y : Fin n → Pt m) (i : Fin 4 ↪ Fin n) :
    {x | VertexGood K T x}.indicator (1 : (Fin 4 → Pt m) → ℝ≥0∞) (y ∘ i) *
      {μ | Feasible K μ (vertexCopy K (y ∘ i))}.indicator 1 (PoissonPP.rest y i) =
    {y | VertexCandidate K T y i}.indicator 1 y := by
  classical
  by_cases hg : VertexGood K T (y ∘ i)
  · have he := vertex_feasible_rest_iff K y i hg.1
    by_cases hf : Feasible K (PoissonPP.config y) (vertexCopy K (y ∘ i))
    · simp [indicator_of_mem, hg, he.mpr hf, VertexCandidate, hf]
    · have hr := mt he.mp hf
      simp [indicator_of_mem, hg, hr, VertexCandidate, hf]
  · have hn : ¬ VertexCandidate K T y i := fun h => hg h.1
    simp [hg, hn]

lemma vertexOrderedCount_eq_lintegral (T : ℝ) :
    vertexOrderedCount K T = ∫⁻ ω, sampleVertexCount K T ω ∂PoissonPP.law (Λ K T) := by
  rw [PoissonPP.lintegral_law _ _ (measurable_sampleVertexCount K T)]
  unfold vertexOrderedCount sampleVertexCount
  congr 1
  funext n
  congr 1
  apply lintegral_congr
  intro y
  exact Finset.sum_congr rfl (fun i _ => candidate_indicator K T y i)

/-- Four-point vertex candidates occur either zero times or in exactly 24 orderings,
outside the proved extra-tight-point null event. Thus their normalized expectation
is an actual probability, rather than merely a candidate-count integral. -/
theorem vertex_candidate_prob (T : ℝ) :
    PoissonPP.law (Λ K T) {ω | HasVertexCandidate K T ω} =
      (1 / 24 : ℝ≥0∞) * vertexOrderedCount K T := by
  have hae : ∀ᵐ ω ∂PoissonPP.law (Λ K T), ¬ BadExtra K (vertexCopy K) ω := by
    rw [ae_iff]
    simpa only [not_not] using no_extra_tight_vertex K T
  have he : vertexOrderedCount K T =
      24 * PoissonPP.law (Λ K T) {ω | HasVertexCandidate K T ω} := by
    rw [vertexOrderedCount_eq_lintegral]
    calc (∫⁻ ω, sampleVertexCount K T ω ∂PoissonPP.law (Λ K T))
        = ∫⁻ ω, 24 * {ω | HasVertexCandidate K T ω}.indicator 1 ω
            ∂PoissonPP.law (Λ K T) := by
          apply lintegral_congr_ae
          filter_upwards [hae] with ω hω
          exact sampleVertexCount_eq K T ω hω
      _ = _ := by
        rw [lintegral_const_mul _ (measurable_one.indicator
          (measurableSet_HasVertexCandidate K T)),
          lintegral_indicator_one (measurableSet_HasVertexCandidate K T)]
  rw [he, ← mul_assoc]
  rw [one_div, ENNReal.inv_mul_cancel (by norm_num) (by norm_num), one_mul]

/-- The finite-depth vertex-candidate probability has the claimed factorization. -/
theorem vertex_candidate_prob_factor (T : ℝ) :
    PoissonPP.law (Λ K T) {ω | HasVertexCandidate K T ω} =
      vertexDensity K * ∫⁻ z : Fin 4 → ℝ, fitWeightBelow K T z := by
  rw [vertex_candidate_prob, vertex_count_factor]

/-- Removal of the cutoff, now for genuine probabilities of vertex-candidate events.
This does not identify every optimum or prove finite-iid-sample convergence. -/
theorem vertex_candidate_prob_limit :
    Filter.Tendsto (fun n : ℕ =>
      PoissonPP.law (Λ K n) {ω | HasVertexCandidate K n ω}) Filter.atTop
      (nhds (vertexDensity K * ∫⁻ z : Fin 4 → ℝ, fitWeight K z)) := by
  simp_rw [vertex_candidate_prob]
  exact vertex_count_limit K

/-- A candidate supplies a fitting unique optimum for the entire sampled configuration. -/
theorem vertex_candidate_unique_optimum (T : ℝ) (ω : PoissonPP.Sample (Pt m))
    (hω : HasVertexCandidate K T ω) :
    ∃ z : Copy, Fits K z ∧ Below K T z ∧ Feasible K (PoissonPP.config ω.2) z ∧
      ∀ z', Feasible K (PoissonPP.config ω.2) z' →
        z.1 ≤ z'.1 ∧ (z'.1 = z.1 → z' = z) := by
  obtain ⟨i, hi⟩ := hω
  refine ⟨vertexCopy K (ω.2 ∘ i), hi.1.2.2.1, hi.1.2.2.2, hi.2, ?_⟩
  intro z' hz'
  have hz := (feasible_config_iff K ω.2 z').mp hz'
  exact ⟨vertexGood_optimal K T _ hi.1 z' (fun r => hz (i r)),
    vertexGood_unique K T _ hi.1 z' (fun r => hz (i r))⟩

end Enclosing
