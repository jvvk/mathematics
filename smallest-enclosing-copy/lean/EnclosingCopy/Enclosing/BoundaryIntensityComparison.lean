import EnclosingCopy.Enclosing.BoundaryMarkLaw
import EnclosingCopy.Poisson.IntensityComparison

/-!
# Removing endpoint margins from the limiting Poisson intensity

Trimming is an exact restriction of the full labelled-strip intensity. The
deleted intensity has mass `2 m δ T / A`, which bounds the error for every
measurable configuration event.
-/
namespace Enclosing
open MeasureTheory Set
variable {m : ℕ}

def trimmedMarkRegion (K : Sides m) (δ : ℝ) : Set (Pt m) :=
  {p | p.2.1 ∈ Icc (K.a p.1 + δ) (K.b p.1 - δ)}

lemma measurableSet_trimmedMarkRegion (K : Sides m) (δ : ℝ) :
    MeasurableSet (trimmedMarkRegion K δ) := by
  have he : trimmedMarkRegion K δ = ⋃ i : Fin m,
      {i} ×ˢ (Icc (K.a i + δ) (K.b i - δ) ×ˢ univ) := by
    ext p; simp [trimmedMarkRegion]
  rw [he]
  exact MeasurableSet.iUnion fun i =>
    (measurableSet_singleton i).prod (measurableSet_Icc.prod MeasurableSet.univ)

lemma trimmedIntensity_eq_full (K : Sides m) (T : ℝ) :
    trimmedIntensity K.a K.b T = Λ K T := by
  rw [trimmedIntensity, Measure.sum_fintype]
  rfl

lemma fullIntensity_restrict_trim (K : Sides m) {δ : ℝ} (hδ : 0 ≤ δ) (T : ℝ) :
    (Λ K T).restrict (trimmedMarkRegion K δ) =
      trimmedIntensity (fun i => K.a i + δ) (fun i => K.b i - δ) T := by
  rw [← trimmedIntensity_eq_full K T, trimmedIntensity,
    Measure.restrict_sum _ (measurableSet_trimmedMarkRegion K δ)]
  congr 1
  funext i
  rw [Measure.dirac_prod, Measure.restrict_map measurable_prodMk_left
    (measurableSet_trimmedMarkRegion K δ), Measure.restrict_restrict
    ((measurableSet_trimmedMarkRegion K δ).preimage measurable_prodMk_left)]
  have he : (Prod.mk i ⁻¹' trimmedMarkRegion K δ) ∩
      (Icc (K.a i) (K.b i) ×ˢ Icc 0 T) =
        Icc (K.a i + δ) (K.b i - δ) ×ˢ Icc 0 T := by
    ext q
    simp only [mem_inter_iff, mem_preimage, trimmedMarkRegion, mem_ofPred_eq,
      mem_prod, mem_Icc]
    constructor
    · rintro ⟨h, _, hdepth⟩; exact ⟨h, hdepth⟩
    · rintro ⟨h, hdepth⟩
      exact ⟨h, ⟨by linarith [h.1], by linarith [h.2]⟩, hdepth⟩
  rw [he, Measure.dirac_prod]

lemma trimmedIntensity_real_mass (a b : Fin m → ℝ) (T : ℝ)
    (hab : ∀ i, a i ≤ b i) (hT : 0 ≤ T) :
    (trimmedIntensity a b T).real univ = ∑ i, (b i - a i) * T := by
  rw [measureReal_def, trimmedIntensity_mass, ENNReal.toReal_sum (fun i _ => by finiteness)]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hT]
  apply Finset.sum_congr rfl
  intro i _
  rw [ENNReal.toReal_ofReal (sub_nonneg.mpr (hab i))]

variable [NeZero m] {v : Fin m → ℝ × ℝ}

/-- Exact lost mass from trimming both ends of each limiting side strip. -/
lemma boundary_deleted_intensity_mass (hm : 3 ≤ m) (hv : ConvexPos v) (harea : area v = 1)
    {δ T : ℝ} (hδ : 0 ≤ δ) (hwidth : ∀ i, aEnd v i + δ ≤ bEnd v i - δ) (hT : 0 ≤ T) :
    let K := sidesOf v hm hv harea
    let A := (volume (polygonRegion K)).toReal
    ((ENNReal.ofReal A⁻¹ • Λ K T).restrict (trimmedMarkRegion K δ)ᶜ).real univ =
      2 * (m : ℝ) * δ * T / A := by
  intro K A
  let μ := ENNReal.ofReal A⁻¹ • Λ K T
  let _ : IsFiniteMeasure μ := ⟨by
    dsimp only [μ]
    rw [Measure.smul_apply, smul_eq_mul]
    finiteness⟩
  have hrestrict : μ.restrict (trimmedMarkRegion K δ) = ENNReal.ofReal A⁻¹ •
      trimmedIntensity (fun i => K.a i + δ) (fun i => K.b i - δ) T := by
    dsimp only [μ]
    rw [Measure.restrict_smul, fullIntensity_restrict_trim K hδ T]
  have hmass : μ.real (trimmedMarkRegion K δ) =
      A⁻¹ * ∑ i, (K.b i - δ - (K.a i + δ)) * T := by
    rw [measureReal_def, ← Measure.restrict_apply_univ, hrestrict,
      Measure.smul_apply, smul_eq_mul, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (inv_nonneg.mpr (physical_area_pos hm hv harea).le)]
    change A⁻¹ * (trimmedIntensity (fun i => K.a i + δ) (fun i => K.b i - δ) T).real univ = _
    rw [trimmedIntensity_real_mass _ _ _ (fun i => show K.a i + δ ≤ K.b i - δ from hwidth i) hT]
  rw [measureReal_def, Measure.restrict_apply_univ, ← measureReal_def,
    measureReal_compl (measurableSet_trimmedMarkRegion K δ), hmass]
  have hfull : μ.real univ = A⁻¹ * ∑ i, (K.b i - K.a i) * T := by
    dsimp only [μ]
    rw [measureReal_def, Measure.smul_apply, smul_eq_mul, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (inv_nonneg.mpr (physical_area_pos hm hv harea).le),
      ← trimmedIntensity_eq_full K T]
    change A⁻¹ * (trimmedIntensity K.a K.b T).real univ = _
    rw [trimmedIntensity_real_mass _ _ _ (fun i => (K.hab i).le) hT]
  rw [hfull, ← mul_sub, ← Finset.sum_sub_distrib]
  simp_rw [show ∀ i : Fin m, (K.b i - K.a i) * T -
      (K.b i - δ - (K.a i + δ)) * T = 2 * δ * T from fun i => by ring]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

/-- Every measurable event in the full Poisson strips is approximated by the trimmed law. -/
theorem poisson_trimmed_event_diff_le (hm : 3 ≤ m) (hv : ConvexPos v) (harea : area v = 1)
    {δ T : ℝ} (hδ : 0 ≤ δ) (hwidth : ∀ i, aEnd v i + δ ≤ bEnd v i - δ) (hT : 0 ≤ T)
    (F : Multiset (Pt m) → Prop)
    (hF : ∀ k, MeasurableSet {x : Fin k → Pt m | F (PoissonPP.config x)}) :
    let K := sidesOf v hm hv harea
    let A := (volume (polygonRegion K)).toReal
    |(PoissonPP.law (ENNReal.ofReal A⁻¹ • Λ K T)).real {ω | F (PoissonPP.config ω.2)} -
      (PoissonPP.law (ENNReal.ofReal A⁻¹ •
        trimmedIntensity (fun i => K.a i + δ) (fun i => K.b i - δ) T)).real
          {ω | F (PoissonPP.config ω.2)}| ≤ 2 * (m : ℝ) * δ * T / A := by
  intro K A
  let μ := ENNReal.ofReal A⁻¹ • Λ K T
  let _ : IsFiniteMeasure μ := ⟨by
    dsimp only [μ]
    rw [Measure.smul_apply, smul_eq_mul]
    finiteness⟩
  have hrestrict : μ.restrict (trimmedMarkRegion K δ) = ENNReal.ofReal A⁻¹ •
      trimmedIntensity (fun i => K.a i + δ) (fun i => K.b i - δ) T := by
    dsimp only [μ]
    rw [Measure.restrict_smul, fullIntensity_restrict_trim K hδ T]
  have hle := PoissonPP.poisson_add_event_diff_le_mass
    (μ.restrict (trimmedMarkRegion K δ)) (μ.restrict (trimmedMarkRegion K δ)ᶜ) F hF
  rw [Measure.restrict_add_restrict_compl (measurableSet_trimmedMarkRegion K δ), hrestrict,
    boundary_deleted_intensity_mass hm hv harea hδ hwidth hT] at hle
  exact hle

end Enclosing
