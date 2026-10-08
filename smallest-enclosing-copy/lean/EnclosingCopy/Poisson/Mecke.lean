import EnclosingCopy.Poisson.Basic
import Mathlib.Data.Fintype.CardEmbedding
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-!
# The multivariate Mecke formula

For the Poisson process with finite intensity `Λ` and a functional `G(x, μ)` of `k` points and a
configuration,

  `E ∑_{(x₁,…,x_k) distinct points of Π} G(x, Π ∖ {x}) = ∫ E G(x, Π) dΛᵏ(x)`

(`mecke`). In the mixed-binomial law, the sum over ordered `k`-tuples of distinct points of a
configuration `{y₀, …, y_{n-1}}` is the sum over injections `i : Fin k ↪ Fin n`, and the rest of
the configuration is `{y_t : t ∉ range i}`.

For each injection the coordinates of `Λⁿ` split, measure-preservingly, into the `k` chosen ones
and the `n - k` others (`split`). There are `n!/(n-k)!` injections, and `e^{-λ}/n! · n!/(n-k)!` is
the Poisson weight of `n - k` points.
-/

namespace PoissonPP

open MeasureTheory ENNReal Set

variable {α : Type*} [MeasurableSpace α] (Λ : Measure α) [IsFiniteMeasure Λ]

/-- The rest of the configuration after removing the points indexed by `i`. -/
def rest {n k : ℕ} (y : Fin n → α) (i : Fin k ↪ Fin n) : Multiset α :=
  (Finset.univ.filter fun t => ¬ ∃ j, i j = t).val.map y

/-- **The split.** `Λⁿ ≅ Λᵏ × Λⁿ⁻ᵏ`, sending `y` to `(y ∘ i, the other coordinates)`. -/
lemma split {n k : ℕ} (i : Fin k ↪ Fin n) :
    ∃ Φ : (Fin n → α) ≃ᵐ (Fin k → α) × (Fin (n - k) → α),
      MeasurePreserving Φ (Measure.pi fun _ => Λ)
        ((Measure.pi fun _ => Λ).prod (Measure.pi fun _ => Λ)) ∧
      ∀ y, (Φ y).1 = y ∘ i ∧ config (Φ y).2 = rest y i := by
  let p : Fin n → Prop := fun t => ∃ j, i j = t
  let eI : Fin k ≃ {t // p t} := Equiv.ofInjective i i.injective
  have hcard : Fintype.card {t // ¬ p t} = n - k := by
    rw [Fintype.card_subtype_compl, Fintype.card_fin, ← Fintype.card_congr eI, Fintype.card_fin]
  let e2 : Fin (n - k) ≃ {t // ¬ p t} := (Fintype.equivFinOfCardEq hcard).symm
  let Φ := (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Fin n => α) p).trans
    (MeasurableEquiv.prodCongr (MeasurableEquiv.piCongrLeft (fun _ => α) eI).symm
      (MeasurableEquiv.piCongrLeft (fun _ => α) e2).symm)
  refine ⟨Φ, ?_, fun y => ⟨?_, ?_⟩⟩
  · exact ((measurePreserving_piCongrLeft (fun _ => Λ) eI).symm _ |>.prod
      ((measurePreserving_piCongrLeft (fun _ => Λ) e2).symm _)).comp
      (measurePreserving_piEquivPiSubtypeProd (fun _ => Λ) p)
  · rfl
  · show Finset.univ.val.map (fun t => y (e2 t)) = _
    rw [show (fun t => y (e2 t)) = (fun s : {t // ¬ p t} => y s) ∘ e2 from rfl, ← Multiset.map_map,
      Multiset.map_univ_val_equiv, rest, ← Finset.univ_val_map_subtype_restrict]
    rfl

/-- The integral of one injection's term. -/
lemma integral_term {n k : ℕ} (i : Fin k ↪ Fin n) (G : (Fin k → α) → Multiset α → ℝ≥0∞)
    (hG : Measurable fun q : (Fin k → α) × (Fin (n - k) → α) => G q.1 (config q.2)) :
    ∫⁻ y, G (y ∘ i) (rest y i) ∂(Measure.pi fun _ => Λ)
      = ∫⁻ x, ∫⁻ z, G x (config z) ∂(Measure.pi fun _ : Fin (n - k) => Λ)
          ∂(Measure.pi fun _ : Fin k => Λ) := by
  obtain ⟨Φ, hΦ, hΦy⟩ := split Λ i
  calc ∫⁻ y, G (y ∘ i) (rest y i) ∂(Measure.pi fun _ => Λ)
      = ∫⁻ y, (fun q : (Fin k → α) × (Fin (n - k) → α) => G q.1 (config q.2)) (Φ y)
          ∂(Measure.pi fun _ => Λ) := by
        refine lintegral_congr fun y => ?_
        simp only [(hΦy y).1, (hΦy y).2]
    _ = ∫⁻ q, G q.1 (config q.2) ∂((Measure.pi fun _ => Λ).prod (Measure.pi fun _ => Λ)) :=
        hΦ.lintegral_comp_emb Φ.measurableEmbedding (fun q => G q.1 (config q.2))
    _ = _ := lintegral_prod _ hG.aemeasurable

lemma term_measurable {n k : ℕ} (i : Fin k ↪ Fin n) (G : (Fin k → α) → Multiset α → ℝ≥0∞)
    (hG : Measurable fun q : (Fin k → α) × (Fin (n - k) → α) => G q.1 (config q.2)) :
    Measurable fun y : Fin n → α => G (y ∘ i) (rest y i) := by
  obtain ⟨Φ, -, hΦy⟩ := split (0 : Measure α) i
  have : (fun y => G (y ∘ i) (rest y i)) = (fun q : (Fin k → α) × (Fin (n - k) → α) =>
      G q.1 (config q.2)) ∘ Φ := by
    funext y; simp only [Function.comp, (hΦy y).1, (hΦy y).2]
  rw [this]
  exact hG.comp Φ.measurable

omit [IsFiniteMeasure Λ] in
/-- `e^{-λ}/(m+k)! · (m+k)!/m! = e^{-λ}/m!`. -/
lemma weight_shift (m k : ℕ) :
    w0 Λ / (m + k).factorial * ((m + k).descFactorial k : ℝ≥0∞) = w0 Λ / m.factorial := by
  have h := Nat.factorial_mul_descFactorial (show k ≤ m + k by omega)
  rw [Nat.add_sub_cancel] at h
  rw [← h, Nat.cast_mul, ENNReal.div_eq_inv_mul, ENNReal.div_eq_inv_mul,
    ENNReal.mul_inv (Or.inr (by simp)) (Or.inr (by simp))]
  have hd : ((m + k).descFactorial k : ℝ≥0∞) ≠ 0 := by
    have : 0 < (m + k).descFactorial k := Nat.descFactorial_pos.2 (by omega)
    exact_mod_cast this.ne'
  calc (↑m.factorial)⁻¹ * (↑((m + k).descFactorial k))⁻¹ * w0 Λ * ↑((m + k).descFactorial k)
      = (↑m.factorial)⁻¹ * w0 Λ * ((↑((m + k).descFactorial k))⁻¹ * ↑((m + k).descFactorial k)) := by
        ring
    _ = (↑m.factorial)⁻¹ * w0 Λ := by
        rw [ENNReal.inv_mul_cancel hd (by simp), mul_one]

/-- **The multivariate Mecke formula** for the Poisson process with finite intensity `Λ`:
`E ∑_{x ∈ Π^k distinct} G(x, Π ∖ x) = ∫ E G(x, Π) dΛᵏ(x)`. -/
theorem mecke (k : ℕ) (G : (Fin k → α) → Multiset α → ℝ≥0∞)
    (hG : ∀ m : ℕ, Measurable fun q : (Fin k → α) × (Fin m → α) => G q.1 (config q.2)) :
    ∑' n : ℕ, w0 Λ / n.factorial * ∫⁻ y, ∑ i : Fin k ↪ Fin n, G (y ∘ i) (rest y i)
        ∂(Measure.pi fun _ => Λ)
      = ∫⁻ x, expect Λ (G x) ∂(Measure.pi fun _ : Fin k => Λ) := by
  set J : ℕ → ℝ≥0∞ := fun m => ∫⁻ x, ∫⁻ z, G x (config z) ∂(Measure.pi fun _ : Fin m => Λ)
    ∂(Measure.pi fun _ : Fin k => Λ)
  -- the `n`-th term is `w0/n! · n.descFactorial k · J (n - k)`
  have hterm : ∀ n : ℕ, w0 Λ / n.factorial * ∫⁻ y, ∑ i : Fin k ↪ Fin n, G (y ∘ i) (rest y i)
      ∂(Measure.pi fun _ => Λ) = w0 Λ / n.factorial * (n.descFactorial k * J (n - k)) := by
    intro n
    rw [lintegral_finset_sum _ fun i _ => term_measurable i G (hG _)]
    simp_rw [integral_term Λ _ G (hG _)]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_embedding_eq, Fintype.card_fin,
      Fintype.card_fin, nsmul_eq_mul]
  simp_rw [hterm]
  -- terms with `n < k` vanish; shift `n = m + k`
  have hzero : Function.support (fun n : ℕ => w0 Λ / n.factorial * (n.descFactorial k * J (n - k)))
      ⊆ range fun m : ℕ => m + k := by
    intro n hn
    by_contra h
    apply hn
    have : n < k := by
      by_contra h'
      exact h ⟨n - k, by simp only; omega⟩
    simp [Nat.descFactorial_eq_zero_iff_lt.2 this]
  rw [← (add_left_injective k).tsum_eq hzero]
  simp only [Nat.add_sub_cancel]
  have : ∀ m : ℕ, w0 Λ / (m + k).factorial * (((m + k).descFactorial k : ℝ≥0∞) * J m)
      = w0 Λ / m.factorial * J m := fun m => by
    rw [← mul_assoc, weight_shift]
  simp_rw [this]
  -- the right side
  unfold expect
  rw [lintegral_tsum fun m => ((hG m).lintegral_prod_right'.const_mul _).aemeasurable]
  congr 1
  funext m
  rw [lintegral_const_mul _ (hG m).lintegral_prod_right']

omit [MeasurableSpace α] [IsFiniteMeasure Λ] in
/-- The void indicator of a configuration, as a cylinder set of the points. -/
lemma void_indicator_config {n : ℕ} (B : Set α) (z : Fin n → α) :
    {μ : Multiset α | ∀ p ∈ μ, p ∉ B}.indicator (1 : Multiset α → ℝ≥0∞) (config z)
      = {z : Fin n → α | ∀ j, z j ∉ B}.indicator 1 z := by
  have hiff : config z ∈ {μ : Multiset α | ∀ p ∈ μ, p ∉ B} ↔ z ∈ {z : Fin n → α | ∀ j, z j ∉ B} := by
    simp [mem_config]
  by_cases h : z ∈ {z : Fin n → α | ∀ j, z j ∉ B}
  · rw [indicator_of_mem (hiff.2 h), indicator_of_mem h]; rfl
  · rw [indicator_of_notMem (fun h' => h (hiff.1 h')), indicator_of_notMem h]

/-- **Mecke with a void condition**, the form used for Theorem 8: the expected number of ordered
`k`-tuples of distinct points `x` with `φ(x)` and no other point in the region `R(x)` is
`∫ φ(x) e^{-Λ(R(x))} dΛᵏ(x)`. -/
theorem mecke_void (k : ℕ) (φ : (Fin k → α) → ℝ≥0∞) (R : (Fin k → α) → Set α)
    (hφ : Measurable φ) (hR : MeasurableSet {q : (Fin k → α) × α | q.2 ∈ R q.1}) :
    ∑' n : ℕ, w0 Λ / n.factorial * ∫⁻ y, ∑ i : Fin k ↪ Fin n,
        φ (y ∘ i) * {μ : Multiset α | ∀ p ∈ μ, p ∉ R (y ∘ i)}.indicator 1 (rest y i)
        ∂(Measure.pi fun _ => Λ)
      = ∫⁻ x, φ x * ENNReal.ofReal (Real.exp (-(Λ (R x)).toReal))
          ∂(Measure.pi fun _ : Fin k => Λ) := by
  have hRx : ∀ x, MeasurableSet (R x) := fun x => measurable_prodMk_left hR
  have hjoint : ∀ m : ℕ, MeasurableSet {q : (Fin k → α) × (Fin m → α) | ∀ j, q.2 j ∉ R q.1} := by
    intro m
    have : {q : (Fin k → α) × (Fin m → α) | ∀ j, q.2 j ∉ R q.1}
        = ⋂ j, (fun q : (Fin k → α) × (Fin m → α) => (q.1, q.2 j)) ⁻¹'
            {q : (Fin k → α) × α | q.2 ∈ R q.1}ᶜ := by
      ext q; simp
    rw [this]
    exact MeasurableSet.iInter fun j =>
      (measurable_fst.prodMk ((measurable_pi_apply j).comp measurable_snd)) hR.compl
  rw [mecke Λ k (fun x μ => φ x * {μ : Multiset α | ∀ p ∈ μ, p ∉ R x}.indicator 1 μ)]
  · refine lintegral_congr fun x => ?_
    have hvoid := void_prob Λ (hRx x)
    unfold prob expect at hvoid
    rw [← hvoid]
    unfold expect
    rw [← ENNReal.tsum_mul_left]
    congr 1
    funext n
    rw [lintegral_const_mul]
    · ring
    · simp_rw [void_indicator_config]
      have hset : {z : Fin n → α | ∀ j, z j ∉ R x} = univ.pi fun _ => (R x)ᶜ := by ext; simp
      rw [hset]
      exact measurable_one.indicator (MeasurableSet.univ_pi fun _ => (hRx x).compl)
  · intro m
    simp_rw [void_indicator_config]
    have : (fun q : (Fin k → α) × (Fin m → α) =>
        {z : Fin m → α | ∀ j, z j ∉ R q.1}.indicator (1 : (Fin m → α) → ℝ≥0∞) q.2)
        = {q : (Fin k → α) × (Fin m → α) | ∀ j, q.2 j ∉ R q.1}.indicator 1 := by
      funext q
      by_cases h : ∀ j, q.2 j ∉ R q.1
      · rw [indicator_of_mem (show q.2 ∈ {z : Fin m → α | ∀ j, z j ∉ R q.1} from h),
          indicator_of_mem (show q ∈ {q : (Fin k → α) × (Fin m → α) | ∀ j, q.2 j ∉ R q.1} from h)]
        rfl
      · rw [indicator_of_notMem (show q.2 ∉ {z : Fin m → α | ∀ j, z j ∉ R q.1} from h),
          indicator_of_notMem (show q ∉ {q : (Fin k → α) × (Fin m → α) | ∀ j, q.2 j ∉ R q.1} from h)]
    exact (hφ.comp measurable_fst).mul (this ▸ measurable_one.indicator (hjoint m))

end PoissonPP
