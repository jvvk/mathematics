import EnclosingCopy.Poisson.Superpose
import Mathlib.Probability.ProductMeasure

/-!
# A Poisson process with locally finite intensity, from independent slabs

Given finite intensities `Λₖ` (`k : ℕ`), the samples `ωₖ` drawn independently from `law Λₖ`
(`Measure.infinitePi`) model a Poisson process with intensity `∑ₖ Λₖ`. Concatenating the first `n`
slabs (`concat n ω`) gives, on every relabelling-invariant functional, the Poisson law with
intensity `∑_{k<n} Λₖ` (`lintegral_concat`, by induction with `superpose_fun`).
-/

namespace PoissonPP
open MeasureTheory Set ENNReal Finset

variable {α : Type*} [MeasurableSpace α]

lemma measurableEmbedding_mk (n : ℕ) :
    MeasurableEmbedding (@Sigma.mk ℕ (fun n => Fin n → α) n) where
  injective := sigma_mk_injective
  measurable := measurable_sampleMk n
  measurableSet_image' T hT := by
    apply measurableSet_sample
    intro k
    by_cases hk : k = n
    · subst hk
      rwa [preimage_image_eq _ sigma_mk_injective]
    · convert MeasurableSet.empty
      ext x
      simp only [Set.mem_preimage, Set.mem_image, mem_empty_iff_false, iff_false]
      rintro ⟨y, -, hyx⟩
      exact hk (congrArg Sigma.fst hyx).symm

/-- Measurable sets of pairs of samples are detected on each pair of lengths. -/
lemma measurableSet_sample2 {S : Set (Sample α × Sample α)}
    (h : ∀ j k, MeasurableSet {q : (Fin j → α) × (Fin k → α) | ((⟨j, q.1⟩ : Sample α), ⟨k, q.2⟩) ∈ S}) :
    MeasurableSet S := by
  have hS : S = ⋃ j : ℕ, ⋃ k : ℕ,
      Prod.map (@Sigma.mk ℕ (fun n => Fin n → α) j) (@Sigma.mk ℕ (fun n => Fin n → α) k) ''
        {q : (Fin j → α) × (Fin k → α) | ((⟨j, q.1⟩ : Sample α), ⟨k, q.2⟩) ∈ S} := by
    ext ⟨⟨j, x⟩, ⟨k, y⟩⟩
    simp only [mem_iUnion, mem_image, Prod.exists, Prod.map, Prod.mk.injEq]
    constructor
    · intro hp; exact ⟨j, k, x, y, hp, rfl, rfl⟩
    · rintro ⟨j', k', x', y', hp, h1, h2⟩
      rw [← h1, ← h2]; exact hp
  rw [hS]
  exact MeasurableSet.iUnion fun j => MeasurableSet.iUnion fun k =>
    ((measurableEmbedding_mk j).prodMap (measurableEmbedding_mk k)).measurableSet_image' (h j k)

lemma measurable_sappend : Measurable fun p : Sample α × Sample α => sappend p.1 p.2 := by
  intro S hS
  apply measurableSet_sample2
  intro j k
  exact ((measurable_sampleMk (j + k)).comp measurable_append) hS

/-- Concatenation of the samples of `n` slabs. -/
def concatFin : (n : ℕ) → (Fin n → Sample α) → Sample α
  | 0, _ => ⟨0, Fin.elim0⟩
  | n + 1, w => sappend (concatFin n (Fin.init w)) (w (Fin.last n))

lemma measurable_concatFin : ∀ n, Measurable (concatFin (α := α) n)
  | 0 => measurable_const
  | n + 1 => measurable_sappend.comp
      (((measurable_concatFin n).comp (measurable_pi_iff.mpr fun i => measurable_pi_apply _)).prodMk
        (measurable_pi_apply _))

omit [MeasurableSpace α] in
lemma mem_config_concatFin : ∀ n (w : Fin n → Sample α) (p : α),
    p ∈ config (concatFin n w).2 ↔ ∃ k, p ∈ config (w k).2
  | 0, w, p => by simp [concatFin, config]
  | n + 1, w, p => by
      simp only [concatFin, sappend, config_append, Multiset.mem_add, mem_config_concatFin n]
      constructor
      · rintro (⟨k, hk⟩ | h)
        · exact ⟨Fin.castSucc k, hk⟩
        · exact ⟨Fin.last n, h⟩
      · rintro ⟨k, hk⟩
        refine Fin.lastCases (fun h => Or.inr h) (fun i h => Or.inl ⟨i, h⟩) k hk

omit [MeasurableSpace α] in
lemma sappend_eq_confFun {f : Sample α → ℝ≥0∞} (hf : PermInv f) (ω₁ ω₂ : Sample α) :
    f (sappend ω₁ ω₂) = confFun f (config ω₁.2 + config ω₂.2) := by
  rw [← config_append, confFun_config hf]; rfl

omit [MeasurableSpace α] in
lemma PermInv.sappend {f : Sample α → ℝ≥0∞} (hf : PermInv f) (ω₂ : Sample α) :
    PermInv fun ω₁ => f (sappend ω₁ ω₂) := by
  intro n x σ
  simp only [sappend_eq_confFun hf]
  rw [config_comp_perm]

/-- The empty sample has the law of the zero intensity. -/
lemma lintegral_law_zero {f : Sample α → ℝ≥0∞} (hm : Measurable f) :
    ∫⁻ ω, f ω ∂law (0 : Measure α) = f ⟨0, Fin.elim0⟩ := by
  rw [lintegral_law _ _ hm, tsum_eq_single 0]
  · simp only [w0, Measure.coe_zero, Pi.zero_apply, ENNReal.toReal_zero, neg_zero, Real.exp_zero,
      ENNReal.ofReal_one, Nat.factorial_zero, Nat.cast_one, div_one, one_mul]
    rw [lintegral_pi_zero (f := fun x => f ⟨0, x⟩) (hm.comp (measurable_sampleMk 0))]
    congr 2
  · intro n hn
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
    have : (Measure.pi fun _ : Fin (k + 1) => (0 : Measure α)) = 0 := by
      rw [← Measure.measure_univ_eq_zero, ← Set.pi_univ, Measure.pi_pi]
      simp
    rw [this, lintegral_zero_measure, mul_zero]

variable (Λs : ℕ → Measure α) [∀ k, IsFiniteMeasure (Λs k)]

/-- **The law of `n` concatenated independent slabs.** -/
theorem lintegral_concatFin (n : ℕ) : ∀ f : Sample α → ℝ≥0∞, PermInv f → Measurable f →
    ∫⁻ w, f (concatFin n w) ∂(Measure.pi fun k : Fin n => law (Λs k)) =
      ∫⁻ ω, f ω ∂law (∑ k : Fin n, Λs k) := by
  induction n with
  | zero =>
    intro f _ hm
    rw [Measure.pi_of_empty, lintegral_dirac' _ (show Measurable fun w : Fin 0 → Sample α =>
      f (concatFin 0 w) from hm.comp (measurable_concatFin 0)),
      Finset.univ_eq_empty, Finset.sum_empty, lintegral_law_zero hm]
    rfl
  | succ n ih =>
    intro f hinv hm
    have hj : Measurable fun p : Sample α × Sample α => f (sappend p.1 p.2) :=
      hm.comp measurable_sappend
    let h : Sample α → ℝ≥0∞ := fun ω₁ => ∫⁻ ω₂, f (sappend ω₁ ω₂) ∂law (Λs n)
    have hhm : Measurable h := hj.lintegral_prod_right'
    have hhinv : PermInv h := by
      intro j x σ
      simp only [h]
      congr 1
      funext ω₂
      exact hinv.sappend ω₂ j x σ
    have he := measurePreserving_piFinSuccAbove (fun k : Fin (n + 1) => law (Λs k)) (Fin.last n)
    have hμ : (Measure.pi fun j : Fin n => law (Λs ((Fin.last n).succAbove j : ℕ))) =
        Measure.pi fun k : Fin n => law (Λs k) := by
      congr 1; funext j; simp [Fin.succAbove_last]
    rw [hμ, show ((Fin.last n : Fin (n + 1)) : ℕ) = n from Fin.val_last n] at he
    have key : ∀ w : Fin (n + 1) → Sample α, f (concatFin (n + 1) w) =
        (fun q : Sample α × (Fin n → Sample α) => f (sappend (concatFin n q.2) q.1))
          (MeasurableEquiv.piFinSuccAbove (fun _ => Sample α) (Fin.last n) w) := by
      intro w
      simp [concatFin, MeasurableEquiv.piFinSuccAbove_apply]
    have hF : Measurable fun q : Sample α × (Fin n → Sample α) => f (sappend (concatFin n q.2) q.1) :=
      hj.comp (((measurable_concatFin n).comp measurable_snd).prodMk measurable_fst)
    calc ∫⁻ w, f (concatFin (n + 1) w) ∂(Measure.pi fun k : Fin (n + 1) => law (Λs k))
        = ∫⁻ q : Sample α × (Fin n → Sample α), f (sappend (concatFin n q.2) q.1)
            ∂((law (Λs n)).prod (Measure.pi fun k : Fin n => law (Λs k))) := by
          simp_rw [key]
          exact he.lintegral_comp hF
      _ = ∫⁻ w, h (concatFin n w) ∂(Measure.pi fun k : Fin n => law (Λs k)) := by
          rw [lintegral_prod_symm _ hF.aemeasurable]
      _ = ∫⁻ ω, h ω ∂law (∑ k : Fin n, Λs k) := ih h hhinv hhm
      _ = ∫⁻ ω, f ω ∂law (∑ k : Fin n, Λs k + Λs n) := superpose_fun _ _ hinv hm
      _ = _ := by rw [Fin.sum_univ_castSucc]; simp

/-- The infinite product of the slab laws. -/
noncomputable def slabLaw : Measure (ℕ → Sample α) := Measure.infinitePi fun k => law (Λs k)

instance : IsProbabilityMeasure (slabLaw Λs) := by unfold slabLaw; infer_instance

/-- The first `n` slabs. -/
def firstSlabs (n : ℕ) (ω : ℕ → Sample α) : Fin n → Sample α := fun k => ω k

lemma measurable_firstSlabs (n : ℕ) : Measurable (firstSlabs (α := α) n) :=
  measurable_pi_iff.mpr fun k => measurable_pi_apply _

lemma map_firstSlabs (n : ℕ) :
    (slabLaw Λs).map (firstSlabs n) = Measure.pi fun k : Fin n => law (Λs k) := by
  refine (Measure.pi_eq fun t ht => ?_).symm
  rw [Measure.map_apply (measurable_firstSlabs n) (MeasurableSet.univ_pi ht)]
  let t' : ℕ → Set (Sample α) := fun j => if h : j < n then t ⟨j, h⟩ else univ
  have hpre : firstSlabs n ⁻¹' univ.pi t = ((Finset.range n : Finset ℕ) : Set ℕ).pi t' := by
    ext ω
    simp only [Set.mem_preimage, firstSlabs, Set.mem_pi, Finset.coe_range, Set.mem_Iio, t']
    constructor
    · intro h j hj; rw [dif_pos hj]; exact h ⟨j, hj⟩ (mem_univ _)
    · intro h k _; have := h k k.2; rw [dif_pos k.2] at this; exact this
  rw [hpre, slabLaw, Measure.infinitePi_pi (X := fun _ : ℕ => Sample α) (μ := fun k => law (Λs k))
    (s := Finset.range n) (t := t') (fun j _ => by
    simp only [t']; split_ifs <;> [exact ht _; exact MeasurableSet.univ])]
  rw [Finset.prod_range fun j => law (Λs j) (t' j)]
  refine Finset.prod_congr rfl fun k _ => ?_
  simp only [t', dif_pos k.2]

/-- **The first `n` slabs of the infinite model** have the Poisson law with intensity
`∑_{k<n} Λₖ` on every relabelling-invariant functional. -/
theorem lintegral_firstSlabs (n : ℕ) {f : Sample α → ℝ≥0∞} (hinv : PermInv f) (hm : Measurable f) :
    ∫⁻ ω, f (concatFin n (firstSlabs n ω)) ∂slabLaw Λs = ∫⁻ ω, f ω ∂law (∑ k : Fin n, Λs k) := by
  rw [← lintegral_concatFin Λs n f hinv hm, ← map_firstSlabs,
    lintegral_map (f := fun w => f (concatFin n w)) (hm.comp (measurable_concatFin n))
      (measurable_firstSlabs n)]

end PoissonPP
