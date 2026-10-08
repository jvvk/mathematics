import EnclosingCopy.Enclosing.Theorem1Model
import EnclosingCopy.Poisson.Superpose

/-!
# Theorem 1: null events affine in one depth

If a function of `k + 1` points is affine in the depth of one of them, with a slope that does
not depend on that depth, then almost surely no `k + 1` distinct sampled points make it vanish
with nonzero slope (`affineDepth_null`). Every "the optimum fits only with equality" event is of
this form: for a vertex optimum, `Hᵢ - Θ e` (with `e` an end of side `i`) is an affine function of
the four depths with a nonzero linear part (`vertex_strict_null`).
-/

namespace Enclosing
open MeasureTheory Set Matrix

variable {m : ℕ} (K : Sides m)

/-- A Lebesgue-null set of positions-and-depths: every depth section has at most one point. -/
theorem intensity_depth_null (T : ℝ) {S : Set (Pt m)} (hS : MeasurableSet S)
    (hsec : ∀ j s, ({D : ℝ | (j, s, D) ∈ S}).Subsingleton) : Λ K T S = 0 := by
  unfold Λ
  rw [Measure.coe_finsetSum, Finset.sum_apply]
  apply Finset.sum_eq_zero
  intro i _
  rw [Measure.dirac_prod, Measure.map_apply measurable_prodMk_left hS]
  apply nonpos_iff_eq_zero.mp
  refine (Measure.restrict_apply_le _ _).trans (le_of_eq ?_)
  have hm : MeasurableSet (Prod.mk i ⁻¹' S) := measurable_prodMk_left hS
  rw [Measure.volume_eq_prod, Measure.measure_prod_null hm]
  refine Filter.Eventually.of_forall fun s => ?_
  exact (hsec i s).measure_zero _

/-- Replace the depth of point `c`. -/
def setDepth {k : ℕ} (w : Fin k → Pt m) (c : Fin k) (D : ℝ) : Fin k → Pt m :=
  Function.update w c ((w c).1, (w c).2.1, D)

/-- `Φ` is affine in the depth of point `c`, with slope `-κ`, and `κ` ignores that depth. -/
structure DepthAffine {k : ℕ} (c : Fin k) (Φ κ : (Fin k → Pt m) → ℝ) : Prop where
  slope : ∀ w D, κ (setDepth w c D) = κ w
  aff : ∀ w D, Φ (setDepth w c D) = Φ (setDepth w c 0) - κ w * D

omit K in
lemma setDepth_setDepth {k : ℕ} (w : Fin k → Pt m) (c : Fin k) (D D' : ℝ) :
    setDepth (setDepth w c D) c D' = setDepth w c D' := by
  funext r
  by_cases h : r = c
  · subst h; simp [setDepth]
  · simp [setDepth, Function.update_of_ne h]

omit K in
lemma snoc_eq_setDepth {k : ℕ} (x : Fin k → Pt m) (j : Fin m) (s D : ℝ) :
    (Fin.snoc x (j, s, D) : Fin (k + 1) → Pt m) =
      setDepth (Fin.snoc x (j, s, 0)) (Fin.last k) D := by
  funext r
  refine Fin.lastCases ?_ (fun i => ?_) r
  · simp [setDepth]
  · simp [setDepth]

omit K in
lemma extraP_snoc {k : ℕ} (Q : (Fin (k + 1) → Pt m) → Prop) (y : Fin (k + 1) → Pt m) :
    extraP (fun x p => Q (Fin.snoc x p)) y ↔ Q y := by
  unfold extraP
  simp only [Fin.succAbove_last]
  rw [show (fun r => y (Fin.castSucc r)) = Fin.init y from rfl, Fin.snoc_init_self]

/-- **The generic null event**, with the free depth on the last point. -/
theorem affineDepth_null_last {k : ℕ} (T : ℝ) {Φ κ : (Fin (k + 1) → Pt m) → ℝ}
    (hΦ : Measurable Φ) (hκ : Measurable κ) (ha : DepthAffine (Fin.last k) Φ κ) :
    PoissonPP.law (Λ K T) {ω | ∃ f : Fin (k + 1) ↪ Fin ω.1,
      κ (ω.2 ∘ f) ≠ 0 ∧ Φ (ω.2 ∘ f) = 0} = 0 := by
  let Q : (Fin (k + 1) → Pt m) → Prop := fun w => κ w ≠ 0 ∧ Φ w = 0
  have hQ : MeasurableSet {w | Q w} :=
    (measurableSet_eq_fun hκ measurable_const).compl.inter
      (measurableSet_eq_fun hΦ measurable_const)
  have hP : MeasurableSet {q : (Fin k → Pt m) × Pt m | Q (Fin.snoc q.1 q.2)} :=
    hQ.preimage PoissonPP.measurable_snoc
  have hnull : ∀ x : Fin k → Pt m, Λ K T {p | Q (Fin.snoc x p)} = 0 := by
    intro x
    apply intensity_depth_null K T (hP.preimage (measurable_const.prodMk measurable_id))
    intro j s D₁ h₁ D₂ h₂
    change Q (Fin.snoc x (j, s, D₁)) at h₁
    change Q (Fin.snoc x (j, s, D₂)) at h₂
    rw [snoc_eq_setDepth] at h₁ h₂
    obtain ⟨hk₁, hz₁⟩ := h₁
    obtain ⟨-, hz₂⟩ := h₂
    rw [ha.slope] at hk₁
    rw [ha.aff] at hz₁ hz₂
    have : κ (Fin.snoc x (j, s, 0)) * (D₁ - D₂) = 0 := by linarith
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left hk₁)
  have h := badP_prob_zero K hP T hnull
  refine le_antisymm (le_of_le_of_eq (measure_mono fun ω hω => ?_) h) bot_le
  obtain ⟨f, hf⟩ := hω
  exact ⟨f, (extraP_snoc Q _).2 hf⟩

omit K in
lemma setDepth_comp_swap {k : ℕ} (w : Fin (k + 1) → Pt m) (c : Fin (k + 1)) (D : ℝ) :
    setDepth w (Fin.last k) D ∘ Equiv.swap c (Fin.last k) =
      setDepth (w ∘ Equiv.swap c (Fin.last k)) c D := by
  funext r
  simp only [setDepth, Function.comp_apply]
  by_cases h : r = c
  · subst h; simp [Equiv.swap_apply_left]
  · have hne : Equiv.swap c (Fin.last k) r ≠ Fin.last k := by
      intro h'
      apply h
      exact (Equiv.swap c (Fin.last k)).injective (h'.trans (Equiv.swap_apply_left c _).symm)
    rw [Function.update_of_ne hne, Function.update_of_ne h]
    rfl

/-- **The generic null event**, with the free depth on any point `c`. -/
theorem affineDepth_null {k : ℕ} (T : ℝ) (c : Fin (k + 1)) {Φ κ : (Fin (k + 1) → Pt m) → ℝ}
    (hΦ : Measurable Φ) (hκ : Measurable κ) (ha : DepthAffine c Φ κ) :
    PoissonPP.law (Λ K T) {ω | ∃ f : Fin (k + 1) ↪ Fin ω.1,
      κ (ω.2 ∘ f) ≠ 0 ∧ Φ (ω.2 ∘ f) = 0} = 0 := by
  let σ := Equiv.swap c (Fin.last k)
  have hσ : Measurable fun w : Fin (k + 1) → Pt m => w ∘ σ :=
    measurable_pi_iff.mpr fun r => measurable_pi_apply _
  have ha' : DepthAffine (Fin.last k) (fun w => Φ (w ∘ σ)) (fun w => κ (w ∘ σ)) := by
    refine ⟨fun w D => ?_, fun w D => ?_⟩
    · simp only [σ, setDepth_comp_swap]; exact ha.slope _ D
    · simp only [σ, setDepth_comp_swap]; exact ha.aff _ D
  have h := affineDepth_null_last K T (hΦ.comp hσ) (hκ.comp hσ) ha'
  refine le_antisymm (le_of_le_of_eq (measure_mono fun ω hω => ?_) h) bot_le
  obtain ⟨f, hf⟩ := hω
  refine ⟨σ.toEmbedding.trans f, ?_⟩
  have e : (ω.2 ∘ ⇑(σ.toEmbedding.trans f)) ∘ ⇑σ = ω.2 ∘ f := by
    funext r; simp [σ, Equiv.swap_apply_self]
  show κ ((ω.2 ∘ ⇑(σ.toEmbedding.trans f)) ∘ ⇑σ) ≠ 0 ∧ Φ ((ω.2 ∘ ⇑(σ.toEmbedding.trans f)) ∘ ⇑σ) = 0
  rw [e]
  exact hf

/-! ### Vertex optima fit strictly -/

/-- The fit slack `Hᵢ - Θ e` as a linear form. -/
def fitForm (i : Fin m) (e : ℝ) : Fin 4 → ℝ := ![K.h i, (K.u i).1, (K.u i).2, -e]

lemma fitForm_copyOfVec (i : Fin m) (e : ℝ) (v : Fin 4 → ℝ) :
    Hs K (copyOfVec v) i - (copyOfVec v).2.2 * e = fitForm K i e ⬝ᵥ v := by
  simp [Hs, dot, copyOfVec, fitForm, dotProduct, Fin.sum_univ_four]; ring

/-- The depth vector of four points, with a sign. -/
def negDepths (w : Fin 4 → Pt m) : Fin 4 → ℝ := fun r => -(w r).2.2

omit K in
lemma negDepths_setDepth (w : Fin 4 → Pt m) (c : Fin 4) (D : ℝ) :
    negDepths (setDepth w c D) = negDepths (setDepth w c 0) + (-D) • Pi.single c 1 := by
  funext r
  by_cases h : r = c
  · subst h; simp [negDepths, setDepth]
  · simp [negDepths, setDepth, h]

lemma vertexMatrix_setDepth (w : Fin 4 → Pt m) (c : Fin 4) (D : ℝ) :
    vertexMatrix K (setDepth w c D) = vertexMatrix K w := by
  funext r q
  by_cases h : r = c
  · subst h; simp [vertexMatrix, row, setDepth]
  · simp [vertexMatrix, setDepth, Function.update_of_ne h]

/-- The slack of the vertex copy. -/
noncomputable def vertexSlack (i : Fin m) (e : ℝ) (w : Fin 4 → Pt m) : ℝ :=
  Hs K (vertexCopy K w) i - (vertexCopy K w).2.2 * e

/-- Its sensitivity to the depth of point `c`. -/
noncomputable def vertexSens (i : Fin m) (e : ℝ) (c : Fin 4) (w : Fin 4 → Pt m) : ℝ :=
  (fitForm K i e ᵥ* (vertexMatrix K w)⁻¹) c

lemma vertexSlack_eq (i : Fin m) (e : ℝ) (w : Fin 4 → Pt m) :
    vertexSlack K i e w = (fitForm K i e ᵥ* (vertexMatrix K w)⁻¹) ⬝ᵥ negDepths w := by
  rw [vertexSlack, vertexCopy, fitForm_copyOfVec, dotProduct_mulVec]
  rfl

lemma vertexSlack_affine (i : Fin m) (e : ℝ) (c : Fin 4) :
    DepthAffine c (vertexSlack K i e) (vertexSens K i e c) := by
  refine ⟨fun w D => ?_, fun w D => ?_⟩
  · simp only [vertexSens, vertexMatrix_setDepth]
  · rw [vertexSlack_eq, vertexSlack_eq, negDepths_setDepth, vertexMatrix_setDepth,
      vertexMatrix_setDepth, dotProduct_add, dotProduct_smul, dotProduct_single_one,
      vertexSens, smul_eq_mul]
    ring

lemma measurable_vertexSlack (i : Fin m) (e : ℝ) : Measurable (vertexSlack K i e) := by
  have h := measurable_vertexCopy K
  have hH : Continuous fun z : Copy => Hs K z i - z.2.2 * e := by
    unfold Hs dot; fun_prop
  exact hH.measurable.comp h

lemma measurable_vertexSens (i : Fin m) (e : ℝ) (c : Fin 4) :
    Measurable (vertexSens K i e c) := by
  have hI := (measurable_matrixInv).comp (measurable_vertexMatrix K)
  have hc : Continuous fun B : Matrix (Fin 4) (Fin 4) ℝ => (fitForm K i e ᵥ* B) c := by
    simp only [vecMul, dotProduct]; fun_prop
  exact hc.measurable.comp hI

/-- With an invertible vertex matrix some depth has nonzero sensitivity. -/
lemma exists_vertexSens_ne (hG : GoodSides K) (i : Fin m) (e : ℝ) {w : Fin 4 → Pt m}
    (hA : (vertexMatrix K w).det ≠ 0) : ∃ c, vertexSens K i e c w ≠ 0 := by
  by_contra h
  push Not at h
  have h0 : fitForm K i e ᵥ* (vertexMatrix K w)⁻¹ = 0 := funext h
  have h1 : fitForm K i e = 0 := by
    have hu : IsUnit (vertexMatrix K w).det := isUnit_iff_ne_zero.mpr hA
    calc fitForm K i e = fitForm K i e ᵥ* ((vertexMatrix K w)⁻¹ * vertexMatrix K w) := by
          rw [Matrix.nonsing_inv_mul _ hu, vecMul_one]
      _ = 0 := by rw [← vecMul_vecMul, h0, zero_vecMul]
  have h2 := congrFun h1 1
  have h3 := congrFun h1 2
  simp [fitForm] at h2 h3
  have := hG.unit i
  rw [h2, h3] at this
  norm_num at this

/-- **A vertex copy of sample points almost surely has no zero fit slack.** -/
theorem vertex_strict_null (hG : GoodSides K) (T : ℝ) (i : Fin m) (e : ℝ) :
    PoissonPP.law (Λ K T) {ω | ∃ f : Fin 4 ↪ Fin ω.1,
      (vertexMatrix K (ω.2 ∘ f)).det ≠ 0 ∧ vertexSlack K i e (ω.2 ∘ f) = 0} = 0 := by
  refine measure_mono_null (t := ⋃ c : Fin 4, {ω | ∃ f : Fin 4 ↪ Fin ω.1,
      vertexSens K i e c (ω.2 ∘ f) ≠ 0 ∧ vertexSlack K i e (ω.2 ∘ f) = 0}) ?_
    (measure_iUnion_null fun c => affineDepth_null K T c (measurable_vertexSlack K i e)
      (measurable_vertexSens K i e c) (vertexSlack_affine K i e c))
  rintro ω ⟨f, hA, hz⟩
  obtain ⟨c, hc⟩ := exists_vertexSens_ne K hG i e hA
  exact Set.mem_iUnion.mpr ⟨c, f, hc, hz⟩

/-! ### Segment optima: relations linear in the segment coordinates -/

section Segment

variable (k kb : Fin m)

/-- The depth vector of three points, with a sign. -/
def negDepths3 (x : Fin 3 → Pt m) : Fin 3 → ℝ := fun r => -(x r).2.2

omit K in
lemma negDepths3_setDepth (x : Fin 3 → Pt m) (c : Fin 3) (D : ℝ) :
    negDepths3 (setDepth x c D) = negDepths3 (setDepth x c 0) + (-D) • Pi.single c 1 := by
  funext r
  by_cases h : r = c
  · subst h; simp [negDepths3, setDepth]
  · simp [negDepths3, setDepth, h]

lemma segMat_setDepth (x : Fin 3 → Pt m) (c : Fin 3) (D : ℝ) :
    segMat K k kb (setDepth x c D) = segMat K k kb x := by
  have : ∀ r, (setDepth x c D r).2.1 = (x r).2.1 := by
    intro r; by_cases h : r = c
    · subst h; simp [setDepth]
    · simp [setDepth, Function.update_of_ne h]
  simp only [segMat, this]

/-- A linear form in the segment coordinates `(ε, w, Θ)`. -/
noncomputable def segLin (ℓ : Fin 3 → ℝ) (x : Fin 3 → Pt m) : ℝ := ℓ ⬝ᵥ segVec K k kb x

noncomputable def segSens (ℓ : Fin 3 → ℝ) (c : Fin 3) (x : Fin 3 → Pt m) : ℝ :=
  (ℓ ᵥ* (segMat K k kb x)⁻¹) c

lemma segLin_eq (ℓ : Fin 3 → ℝ) (x : Fin 3 → Pt m) :
    segLin K k kb ℓ x = (ℓ ᵥ* (segMat K k kb x)⁻¹) ⬝ᵥ negDepths3 x := by
  rw [segLin, segVec, dotProduct_mulVec]; rfl

lemma segLin_affine (ℓ : Fin 3 → ℝ) (c : Fin 3) :
    DepthAffine c (segLin K k kb ℓ) (segSens K k kb ℓ c) := by
  refine ⟨fun w D => ?_, fun w D => ?_⟩
  · simp only [segSens, segMat_setDepth]
  · rw [segLin_eq, segLin_eq, negDepths3_setDepth, segMat_setDepth, segMat_setDepth,
      dotProduct_add, dotProduct_smul, dotProduct_single_one, segSens, smul_eq_mul]
    ring

lemma measurable_segLin (ℓ : Fin 3 → ℝ) : Measurable (segLin K k kb ℓ) := by
  have hc : Continuous fun v : Fin 3 → ℝ => ℓ ⬝ᵥ v := by
    simp only [dotProduct]; fun_prop
  exact hc.measurable.comp (measurable_segVec K k kb)

lemma measurable_segSens (ℓ : Fin 3 → ℝ) (c : Fin 3) : Measurable (segSens K k kb ℓ c) := by
  have hI := measurable_matrixInv3.comp (measurable_segMat K k kb)
  have hc : Continuous fun B : Matrix (Fin 3) (Fin 3) ℝ => (ℓ ᵥ* B) c := by
    simp only [vecMul, dotProduct]; fun_prop
  exact hc.measurable.comp hI

lemma exists_segSens_ne {ℓ : Fin 3 → ℝ} (hℓ : ℓ ≠ 0) {x : Fin 3 → Pt m}
    (hM : (segMat K k kb x).det ≠ 0) : ∃ c, segSens K k kb ℓ c x ≠ 0 := by
  by_contra h
  push Not at h
  have h0 : ℓ ᵥ* (segMat K k kb x)⁻¹ = 0 := funext h
  apply hℓ
  have hu : IsUnit (segMat K k kb x).det := isUnit_iff_ne_zero.mpr hM
  calc ℓ = ℓ ᵥ* ((segMat K k kb x)⁻¹ * segMat K k kb x) := by
        rw [Matrix.nonsing_inv_mul _ hu, vecMul_one]
    _ = 0 := by rw [← vecMul_vecMul, h0, zero_vecMul]

/-- **A nonzero linear form in the segment coordinates of three sample points almost surely
does not vanish.** -/
theorem segLin_null (T : ℝ) {ℓ : Fin 3 → ℝ} (hℓ : ℓ ≠ 0) :
    PoissonPP.law (Λ K T) {ω | ∃ f : Fin 3 ↪ Fin ω.1,
      (segMat K k kb (ω.2 ∘ f)).det ≠ 0 ∧ segLin K k kb ℓ (ω.2 ∘ f) = 0} = 0 := by
  refine measure_mono_null (t := ⋃ c : Fin 3, {ω | ∃ f : Fin 3 ↪ Fin ω.1,
      segSens K k kb ℓ c (ω.2 ∘ f) ≠ 0 ∧ segLin K k kb ℓ (ω.2 ∘ f) = 0}) ?_
    (measure_iUnion_null fun c => affineDepth_null K T c (measurable_segLin K k kb ℓ)
      (measurable_segSens K k kb ℓ c) (segLin_affine K k kb ℓ c))
  rintro ω ⟨f, hM, hz⟩
  obtain ⟨c, hc⟩ := exists_segSens_ne K k kb hℓ hM
  exact Set.mem_iUnion.mpr ⟨c, f, hc, hz⟩

/-- The fit slack `Hᵢ(segCopy v c) - Θ e` is `segFitLin i e ⬝ᵥ v + c tᵢ`. -/
def segFitLin (i : Fin m) (e : ℝ) : Fin 3 → ℝ := ![K.h i, dot (K.u k) (K.u i), -e]

/-- The slope of side `i` along the segment. -/
def segSlope (i : Fin m) : ℝ := dot (K.u i) (tang K k)

lemma Hs_segCopy (v : Fin 3 → ℝ) (c : ℝ) (i : Fin m) (e : ℝ) :
    Hs K (segCopy K k v c) i - (segCopy K k v c).2.2 * e =
      segFitLin K k i e ⬝ᵥ v + c * segSlope K k i := by
  simp [Hs, segCopy, chordCopy, dot, segFitLin, segSlope, tang, dotProduct, Fin.sum_univ_three]
  ring

/-- The point `p = (j, s, D)` is tight on the segment line at `c` iff
`segFitLin j s ⬝ᵥ v + c tⱼ + D = 0`. -/
lemma gx_segCopy_lin (v : Fin 3 → ℝ) (c : ℝ) (p : Pt m) :
    gx K (segCopy K k v c) p = segFitLin K k p.1 p.2.1 ⬝ᵥ v + c * segSlope K k p.1 + p.2.2 := by
  rw [gx, ← Hs_segCopy]

/-- **A kink of the fit slack meets the end of the feasible chord** only on a null event: the
end is fixed by a fourth point whose depth enters with slope `1/tⱼ`. -/
noncomputable def kinkEnd (i : Fin m) (e : ℝ) (w : Fin 4 → Pt m) : ℝ :=
  -(segFitLin K k (w 3).1 (w 3).2.1 ⬝ᵥ segVec K k kb (w ∘ Fin.castSucc) + (w 3).2.2) *
      (segSlope K k (w 3).1)⁻¹ +
    (segFitLin K k i e ⬝ᵥ segVec K k kb (w ∘ Fin.castSucc)) * (segSlope K k i)⁻¹

noncomputable def kinkEndSens (w : Fin 4 → Pt m) : ℝ := (segSlope K k (w 3).1)⁻¹

lemma setDepth_last_castSucc (w : Fin 4 → Pt m) (D : ℝ) :
    setDepth w 3 D ∘ Fin.castSucc = w ∘ Fin.castSucc := by
  funext r
  have hr : (Fin.castSucc r : Fin 4) ≠ 3 := by fin_cases r <;> decide
  simp [setDepth, Function.update_of_ne hr]

lemma kinkEnd_affine (i : Fin m) (e : ℝ) :
    DepthAffine (3 : Fin 4) (kinkEnd K k kb i e) (kinkEndSens K k) := by
  refine ⟨fun w D => ?_, fun w D => ?_⟩
  · simp [kinkEndSens, setDepth]
  · simp only [kinkEnd, kinkEndSens, setDepth_last_castSucc]
    simp [setDepth]
    ring

lemma measurable_kinkEnd (i : Fin m) (e : ℝ) : Measurable (kinkEnd K k kb i e) := by
  have hv : Measurable fun w : Fin 4 → Pt m => segVec K k kb (w ∘ Fin.castSucc) :=
    (measurable_segVec K k kb).comp (measurable_pi_iff.mpr fun r => measurable_pi_apply _)
  have h3 : Measurable fun w : Fin 4 → Pt m => w 3 := measurable_pi_apply 3
  have hside : Measurable fun w : Fin 4 → Pt m => (w 3).1 := measurable_fst.comp h3
  have hpos : Measurable fun w : Fin 4 → Pt m => (w 3).2.1 :=
    measurable_fst.comp (measurable_snd.comp h3)
  have hdep : Measurable fun w : Fin 4 → Pt m => (w 3).2.2 :=
    measurable_snd.comp (measurable_snd.comp h3)
  have hL : Measurable fun w : Fin 4 → Pt m =>
      segFitLin K k (w 3).1 (w 3).2.1 ⬝ᵥ segVec K k kb (w ∘ Fin.castSucc) := by
    have : Measurable fun q : (ℝ × (Fin 3 → ℝ)) × Fin m => segFitLin K k q.2 q.1.1 ⬝ᵥ q.1.2 := by
      apply measurable_from_prod_countable_left
      intro j
      have hc : Continuous fun q : ℝ × (Fin 3 → ℝ) => segFitLin K k j q.1 ⬝ᵥ q.2 := by
        simp only [segFitLin, dotProduct, Fin.sum_univ_three]
        simp; fun_prop
      exact hc.measurable
    exact this.comp ((hpos.prodMk hv).prodMk hside)
  have hS : Measurable fun w : Fin 4 → Pt m => (segSlope K k (w 3).1)⁻¹ :=
    (Measurable.of_discrete (f := fun j : Fin m => (segSlope K k j)⁻¹)).comp hside
  have hc : Continuous fun v : Fin 3 → ℝ => segFitLin K k i e ⬝ᵥ v := by
    simp only [dotProduct]; fun_prop
  exact (((hL.add hdep).neg).mul hS).add ((hc.measurable.comp hv).mul measurable_const)

lemma measurable_kinkEndSens : Measurable (kinkEndSens K k) :=
  (Measurable.of_discrete (f := fun j : Fin m => (segSlope K k j)⁻¹)).comp
    (measurable_fst.comp (measurable_pi_apply 3))

theorem kinkEnd_null (T : ℝ) (i : Fin m) (e : ℝ) :
    PoissonPP.law (Λ K T) {ω | ∃ f : Fin 4 ↪ Fin ω.1,
      kinkEndSens K k (ω.2 ∘ f) ≠ 0 ∧ kinkEnd K k kb i e (ω.2 ∘ f) = 0} = 0 :=
  affineDepth_null K T 3 (measurable_kinkEnd K k kb i e) (measurable_kinkEndSens K k)
    (kinkEnd_affine K k kb i e)

end Segment

end Enclosing
