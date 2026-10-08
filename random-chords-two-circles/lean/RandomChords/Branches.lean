import RandomChords.Basic

/-!
# Laws by inverse branches

The proofs of Lemmas 1 and 2 compute a change of variables in the reverse direction: from the angles
`x` (in an open square `s`) back to the polar angles of the two points. There are finitely many
inverse branches `ψ i`. Each branch lands in a fixed window of length `2π` in each coordinate, so it
can be pushed to `Ang × Ang` without losing injectivity; its Jacobian `J i` is computed on its domain
and vanishes on the rest of `s`. If the Jacobians add up to a constant `c` with `c · |s|` equal to the
total mass of `Ang × Ang`, then the branches cover `Ang × Ang` up to a null set and the angle map `F`
pushes `volume` to `c • volume` on `s`. This is the paper's "summing the contributions" step.
-/

open Real MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace Chords

/-- The covering map `ℝ² → Ang × Ang`. -/
def proj (x : ℝ × ℝ) : Ang × Ang := ((x.1 : Ang), (x.2 : Ang))

lemma continuous_proj : Continuous proj :=
  ((AddCircle.continuous_mk' _).comp continuous_fst).prodMk
    ((AddCircle.continuous_mk' _).comp continuous_snd)

/-- The window `(t₁, t₁ + 2π] × (t₂, t₂ + 2π]`. -/
def box (t : ℝ × ℝ) : Set (ℝ × ℝ) := Ioc t.1 (t.1 + 2 * π) ×ˢ Ioc t.2 (t.2 + 2 * π)

lemma measurePreserving_proj (t : ℝ × ℝ) :
    MeasurePreserving proj (volume.restrict (box t)) volume := by
  have h := (AddCircle.measurePreserving_mk (2 * π) t.1).prod
    (AddCircle.measurePreserving_mk (2 * π) t.2)
  rw [Measure.prod_restrict, ← Measure.volume_eq_prod] at h
  exact h

lemma injOn_proj (t : ℝ × ℝ) : InjOn proj (box t) := by
  rintro x hx y hy h
  simp only [proj, Prod.mk.injEq] at h
  exact Prod.ext ((AddCircle.coe_eq_coe_iff_of_mem_Ioc hx.1 hy.1).1 h.1)
    ((AddCircle.coe_eq_coe_iff_of_mem_Ioc hx.2 hy.2).1 h.2)

lemma proj_image (t : ℝ × ℝ) {Y : Set (ℝ × ℝ)} (hY : MeasurableSet Y) (hYb : Y ⊆ box t) :
    MeasurableSet (proj '' Y) ∧ volume (proj '' Y) = volume Y := by
  have hm : MeasurableSet (proj '' Y) :=
    hY.image_of_continuousOn_injOn continuous_proj.continuousOn ((injOn_proj t).mono hYb)
  refine ⟨hm, ?_⟩
  rw [← (measurePreserving_proj t).measure_preimage hm.nullMeasurableSet,
    Measure.restrict_apply (hm.preimage continuous_proj.measurable)]
  congr 1
  ext x
  constructor
  · rintro ⟨⟨y, hy, hxy⟩, hx⟩
    rwa [← injOn_proj t (hYb hy) hx hxy]
  · intro hx
    exact ⟨⟨x, hx, rfl⟩, hYb hx⟩

/-- The branch theorem. -/
theorem map_eq_of_branches {ι : Type*} [Fintype ι] (F : Ang × Ang → ℝ × ℝ) (hF : Measurable F)
    (s : Set (ℝ × ℝ)) (hs : MeasurableSet s) (c : ℝ≥0∞)
    (ψ : ι → ℝ × ℝ → ℝ × ℝ) (ψ' : ι → ℝ × ℝ → (ℝ × ℝ →L[ℝ] ℝ × ℝ))
    (dom : ι → Set (ℝ × ℝ)) (hdom : ∀ i, MeasurableSet (dom i)) (hdoms : ∀ i, dom i ⊆ s)
    (t : ι → ℝ × ℝ) (hbox : ∀ i, MapsTo (ψ i) (dom i) (box (t i)))
    (hderiv : ∀ i, ∀ x ∈ dom i, HasFDerivWithinAt (ψ i) (ψ' i x) (dom i) x)
    (hinv : ∀ i, ∀ x ∈ dom i, F (proj (ψ i x)) = x)
    (hdisj : ∀ i j, i ≠ j → ∀ x ∈ dom i, x ∈ dom j → proj (ψ i x) ≠ proj (ψ j x))
    (J : ι → ℝ × ℝ → ℝ≥0∞) (hJm : ∀ i, Measurable (J i))
    (hJ : ∀ i, ∀ x ∈ dom i, ENNReal.ofReal |(ψ' i x).det| = J i x)
    (hJ0 : ∀ i, ∀ x ∈ s \ dom i, J i x = 0)
    (hsum : ∀ x ∈ s, ∑ i, J i x = c)
    (htot : c * volume s = volume (univ : Set (Ang × Ang))) :
    Measure.map F volume = c • volume.restrict s ∧
      ∀ᵐ ω ∂(volume : Measure (Ang × Ang)), ∃ i, ∃ x ∈ dom i, ω = proj (ψ i x) := by
  have : (volume : Measure (ℝ × ℝ)).IsAddHaarMeasure := by
    rw [Measure.volume_eq_prod]; infer_instance
  -- the pieces
  set I : ι → Set (ℝ × ℝ) → Set (Ang × Ang) := fun i E => proj '' (ψ i '' (dom i ∩ E)) with hI
  have hinj : ∀ i, InjOn (ψ i) (dom i) := by
    intro i x hx y hy h
    rw [← hinv i x hx, ← hinv i y hy, h]
  have hpiece : ∀ i E, MeasurableSet E →
      MeasurableSet (I i E) ∧ volume (I i E) = ∫⁻ x in dom i ∩ E, J i x := by
    intro i E hE
    have hDE : MeasurableSet (dom i ∩ E) := (hdom i).inter hE
    have hd : ∀ x ∈ dom i ∩ E, HasFDerivWithinAt (ψ i) (ψ' i x) (dom i ∩ E) x :=
      fun x hx => (hderiv i x hx.1).mono inter_subset_left
    have hY : MeasurableSet (ψ i '' (dom i ∩ E)) :=
      measurable_image_of_fderivWithin hDE hd ((hinj i).mono inter_subset_left)
    obtain ⟨hm, hv⟩ := proj_image (t i) hY (by
      rintro _ ⟨x, hx, rfl⟩; exact hbox i hx.1)
    refine ⟨hm, ?_⟩
    rw [hv, ← setLIntegral_one,
      lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hDE hd
        ((hinj i).mono inter_subset_left)]
    refine setLIntegral_congr_fun hDE (fun x hx => ?_)
    simp [hJ i x hx.1]
  -- each piece integral can be taken over `s ∩ E`
  have hext : ∀ i E, MeasurableSet E →
      ∫⁻ x in dom i ∩ E, J i x = ∫⁻ x in s ∩ E, J i x := by
    intro i E hE
    have h1 : ∫⁻ x in s ∩ E, J i x = ∫⁻ x in s ∩ E, (dom i).indicator (J i) x := by
      refine setLIntegral_congr_fun (hs.inter hE) (fun x hx => ?_)
      by_cases hxd : x ∈ dom i
      · simp [hxd]
      · simp [hxd, hJ0 i x ⟨hx.1, hxd⟩]
    rw [h1, lintegral_indicator (hdom i), Measure.restrict_restrict (hdom i)]
    congr 2
    ext x
    constructor
    · rintro ⟨hx, hxE⟩; exact ⟨hx, hdoms i hx, hxE⟩
    · rintro ⟨hx, _, hxE⟩; exact ⟨hx, hxE⟩
  have hdisjI : ∀ E E', Pairwise (fun i j => Disjoint (I i E) (I j E')) := by
    intro E E' i j hij
    rw [Set.disjoint_left]
    rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩ ⟨_, ⟨y, hy, rfl⟩, hxy⟩
    have : y = x := by rw [← hinv j y hy.1, hxy, hinv i x hx.1]
    subst this
    exact hdisj i j hij y hx.1 hy.1 hxy.symm
  have hunion : ∀ E, MeasurableSet E →
      volume (⋃ i, I i E) = c * volume (s ∩ E) := by
    intro E hE
    rw [measure_iUnion (hdisjI E E) (fun i => (hpiece i E hE).1)]
    simp_rw [fun i => (hpiece i E hE).2, fun i => hext i E hE]
    rw [tsum_fintype, ← lintegral_finsetSum _ (fun i _ => hJm i)]
    rw [setLIntegral_congr_fun (hs.inter hE) (fun x hx => hsum x hx.1)]
    rw [setLIntegral_const, mul_comm]
  -- the union of the pieces is conull
  set U := ⋃ i, I i univ with hU
  have hUm : MeasurableSet U := MeasurableSet.iUnion (fun i => (hpiece i univ MeasurableSet.univ).1)
  have hUc : volume Uᶜ = 0 := by
    have hfin : volume (univ : Set (Ang × Ang)) ≠ ∞ := measure_ne_top _ _
    have h := hunion univ MeasurableSet.univ
    rw [inter_univ, htot] at h
    rw [measure_compl hUm (measure_ne_top _ _), h, tsub_self]
  have hae : ∀ᵐ ω ∂(volume : Measure (Ang × Ang)), ω ∈ U := by
    rw [ae_iff]; simpa [compl_def] using hUc
  refine ⟨?_, ?_⟩
  · refine Measure.ext fun E hE => ?_
    rw [Measure.map_apply hF hE, Measure.smul_apply, Measure.restrict_apply hE, smul_eq_mul,
      inter_comm E s, ← hunion E hE]
    have hsets : F ⁻¹' E ∩ U = ⋃ i, I i E := by
      ext ω
      simp only [hU, hI, mem_inter_iff, mem_preimage, mem_iUnion, mem_image]
      constructor
      · rintro ⟨hω, i, _, ⟨x, ⟨hx, -⟩, rfl⟩, rfl⟩
        refine ⟨i, ψ i x, ⟨x, ⟨hx, ?_⟩, rfl⟩, rfl⟩
        rwa [hinv i x hx] at hω
      · rintro ⟨i, _, ⟨x, ⟨hx, hxE⟩, rfl⟩, rfl⟩
        exact ⟨by rwa [hinv i x hx], i, ψ i x, ⟨x, ⟨hx, trivial⟩, rfl⟩, rfl⟩
    rw [← hsets, measure_inter_conull hUc]
  · filter_upwards [hae] with ω hω
    simp only [hU, hI, mem_iUnion, mem_image] at hω
    obtain ⟨i, _, ⟨x, ⟨hx, -⟩, rfl⟩, rfl⟩ := hω
    exact ⟨i, x, hx, rfl⟩

end Chords
