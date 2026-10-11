import LeanProofs.AcuteTetra.Count
import LeanProofs.AcuteTetra.Pair

/-!
# Acute tetrahedron: the probability is `1/12`

Four independent uniform points `A 0, …, A 3` on the unit sphere (`PP = unif^⊗4`).

* Signed relabellings `A ↦ (m ↦ ±A (pm m))` preserve `PP` (`sp_mp`).
* `P(F_l) = α = 1/6` and `P(F_l ∩ F_l') = γ = 1/24` for the face sums `F_l` of `T_∅`.
* Configurations are generic (unit vectors, no signed triple sum of norm `1`) almost surely.
* Integrating `N + C = 8` (Lemma 4) and `[1 ≤ k ≤ 2] + C(k,2) = k` gives `16p + 16r = 8`,
  `r + 6γ = 4α`, hence `p = 1/12`.
-/

namespace AcuteTetra

open MeasureTheory Real Set Metric

abbrev Ω := Fin 4 → E3

/-- Four independent uniform points on the unit sphere. -/
noncomputable def PP : Measure Ω := Measure.pi fun _ => unif

instance : IsProbabilityMeasure PP := by unfold PP; infer_instance

/-! ## Symmetries -/

/-- `x ↦ ±x` as a linear isometry. -/
noncomputable def sgnLI (b : Bool) : E3 ≃ₗᵢ[ℝ] E3 :=
  if b then LinearIsometryEquiv.refl ℝ E3 else LinearIsometryEquiv.neg ℝ

lemma sgnLI_apply (b : Bool) (x : E3) : sgnLI b x = (sgZ b : ℝ) • x := by
  cases b <;> simp [sgnLI, sgZ]

lemma sgnLI_mp (b : Bool) : MeasurePreserving (sgnLI b) unif unif :=
  ⟨(sgnLI b).continuous.measurable, unif_map _⟩

/-- The signed relabelling `A ↦ (m ↦ τ_m A (pm m))`. -/
noncomputable def sp (pm : Equiv.Perm (Fin 4)) (τ : Sign) : Ω ≃ᵐ Ω :=
  (MeasurableEquiv.piCongrLeft (fun _ => E3) pm.symm).trans
    (MeasurableEquiv.piCongrRight fun m => (sgnLI (τ m)).toHomeomorph.toMeasurableEquiv)

lemma sp_apply (pm : Equiv.Perm (Fin 4)) (τ : Sign) (A : Ω) (m : Fin 4) :
    sp pm τ A m = (sgZ (τ m) : ℝ) • A (pm m) := by
  have h : MeasurableEquiv.piCongrLeft (fun _ => E3) pm.symm A m = A (pm m) := by
    have := MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ => E3) pm.symm A (pm m)
    simpa using this
  change sgnLI (τ m) (MeasurableEquiv.piCongrLeft (fun _ => E3) pm.symm A m) = _
  rw [h]
  exact sgnLI_apply _ _

lemma sp_mp (pm : Equiv.Perm (Fin 4)) (τ : Sign) : MeasurePreserving (sp pm τ) PP PP := by
  have h1 := measurePreserving_piCongrLeft (fun _ : Fin 4 => unif) pm.symm
  have h2 := measurePreserving_pi (fun _ : Fin 4 => unif) (fun _ => unif)
    (fun m => sgnLI_mp (τ m))
  exact h2.comp h1

lemma PP_sp (pm : Equiv.Perm (Fin 4)) (τ : Sign) (S : Set Ω) : PP (sp pm τ ⁻¹' S) = PP S :=
  (sp_mp pm τ).measure_preimage_equiv S

/-! ## Two canonical events, by Fubini -/

/-- `A ↦ (A 3, (A 2, (A 0, A 1)))`. -/
noncomputable def Φ (A : Ω) : E3 × (E3 × (E3 × E3)) := (A 3, (A 2, (A 0, A 1)))

lemma Φ_mp : MeasurePreserving Φ PP (unif.prod (unif.prod (unif.prod unif))) := by
  have m4 := measurePreserving_piFinSuccAbove (fun _ : Fin 4 => unif) 3
  have m3 := measurePreserving_piFinSuccAbove (fun _ : Fin 3 => unif) 2
  have m2 := measurePreserving_finTwoArrow (unif : Measure E3)
  have := ((MeasurePreserving.id unif).prod ((MeasurePreserving.id unif).prod m2)).comp
    (((MeasurePreserving.id unif).prod m3).comp m4)
  unfold PP
  convert this using 1
  funext A
  rfl

lemma PP_F3 : PP {A | ‖A 0 + A 1 + A 2‖ < 1} = ENNReal.ofReal (1 / 6) := by
  have hS' : MeasurableSet {y : E3 × (E3 × E3) | ‖y.2.1 + y.2.2 + y.1‖ < 1} :=
    measurableSet_lt (by fun_prop) measurable_const
  have : {A : Ω | ‖A 0 + A 1 + A 2‖ < 1} =
      Φ ⁻¹' (univ ×ˢ {y : E3 × (E3 × E3) | ‖y.2.1 + y.2.2 + y.1‖ < 1}) := by
    ext A; simp [Φ]
  rw [this, Φ_mp.measure_preimage (MeasurableSet.univ.prod hS').nullMeasurableSet,
    Measure.prod_prod, measure_univ, one_mul, Measure.prod_apply_symm hS', ← alpha_eq]
  rfl

lemma PP_F3F2 : PP {A | ‖A 0 + A 1 + A 2‖ < 1 ∧ ‖A 0 + A 1 + A 3‖ < 1} =
    ENNReal.ofReal (1 / 24) := by
  set S' := {y : E3 × (E3 × E3) | ‖y.2.1 + y.2.2 + y.1‖ < 1} with hS'def
  have hS' : MeasurableSet S' := measurableSet_lt (by fun_prop) measurable_const
  set S := {x : E3 × (E3 × (E3 × E3)) | x.2 ∈ S' ∧ ‖x.2.2.1 + x.2.2.2 + x.1‖ < 1} with hSdef
  have hS : MeasurableSet S :=
    (measurable_snd hS').inter (measurableSet_lt
      (by fun_prop : Measurable fun x : E3 × (E3 × (E3 × E3)) => ‖x.2.2.1 + x.2.2.2 + x.1‖)
      measurable_const)
  have : {A : Ω | ‖A 0 + A 1 + A 2‖ < 1 ∧ ‖A 0 + A 1 + A 3‖ < 1} = Φ ⁻¹' S := by
    ext A; simp [Φ, hSdef, hS'def]
  rw [this, Φ_mp.measure_preimage hS.nullMeasurableSet, Measure.prod_apply_symm hS]
  have hslice : ∀ y : E3 × (E3 × E3), unif ((fun d => (d, y)) ⁻¹' S) =
      S'.indicator (fun y => q y.2.1 y.2.2) y := by
    intro y
    by_cases hy : y ∈ S'
    · rw [indicator_of_mem hy, q]
      congr 1; ext d; simp [hSdef, hy]
    · rw [indicator_of_notMem hy]
      convert measure_empty (μ := unif)
      ext d; simp [hSdef, hy]
  simp only [hslice]
  rw [lintegral_prod_symm _ ((Measurable.indicator (f := fun y : E3 × (E3 × E3) => q y.2.1 y.2.2)
    (q_meas.comp measurable_snd) hS').aemeasurable),
    ← gamma_eq]
  refine lintegral_congr fun p => ?_
  have : (fun c => S'.indicator (fun y : E3 × (E3 × E3) => q y.2.1 y.2.2) (c, p)) =
      {c : E3 | ‖p.1 + p.2 + c‖ < 1}.indicator fun _ => q p.1 p.2 := by
    funext c; simp [indicator, hS'def]
  rw [this, lintegral_indicator_const (measurableSet_lt (by fun_prop) measurable_const), ← q, sq,
    mul_comm]

/-! ## Relabelling to the canonical events -/

/-- The all-`+` sign vector: the tetrahedron `T_∅ = (A 0, A 1, A 2, A 3)`. -/
def allTrue : Sign := fun _ => true

/-- `F_l`: the face sum of `T_∅` opposite `l` is short. -/
def Fl (l : Fin 4) : Set Ω := {A | ‖faceSum A allTrue l‖ < 1}

lemma faceSum_allTrue (A : Ω) (l : Fin 4) :
    faceSum A allTrue l = ∑ i, (if i = l then (0 : ℝ) else 1) • A i := by
  simp only [faceSum, vecOf, cDrop, allTrue, sgZ, ite_true]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs <;> simp

lemma faceSum_perm (A : Ω) (pm : Equiv.Perm (Fin 4)) (k : Fin 4) :
    ∑ m, (if m = k then (0 : ℝ) else 1) • sp pm allTrue A m = faceSum A allTrue (pm k) := by
  rw [faceSum_allTrue, ← Equiv.sum_comp pm (fun i => (if i = pm k then (0 : ℝ) else 1) • A i)]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [sp_apply]
  simp [allTrue, sgZ, pm.injective.eq_iff]

lemma faceSum_three (B : Ω) : ∑ m, (if m = (3 : Fin 4) then (0 : ℝ) else 1) • B m = B 0 + B 1 + B 2 := by
  simp [Fin.sum_univ_four]

lemma faceSum_two (B : Ω) : ∑ m, (if m = (2 : Fin 4) then (0 : ℝ) else 1) • B m = B 0 + B 1 + B 3 := by
  simp [Fin.sum_univ_four]

lemma swap_two (l l' : Fin 4) (h : l ≠ l') :
    ((Equiv.swap 3 l) * Equiv.swap 2 (Equiv.swap 3 l l')) 2 = l' := by
  revert l l'; decide

lemma swap_three (l l' : Fin 4) (h : l ≠ l') :
    ((Equiv.swap 3 l) * Equiv.swap 2 (Equiv.swap 3 l l')) 3 = l := by
  revert l l'; decide

/-- `P(F_l) = α = 1/6`. -/
theorem PP_Fl (l : Fin 4) : PP (Fl l) = ENNReal.ofReal (1 / 6) := by
  have : Fl l = sp (Equiv.swap 3 l) allTrue ⁻¹' {A | ‖A 0 + A 1 + A 2‖ < 1} := by
    ext A
    simp only [Fl, mem_preimage, mem_ofPred_eq, ← faceSum_three, faceSum_perm]
    simp
  rw [this, PP_sp, PP_F3]

/-- `P(F_l ∩ F_l') = γ = 1/24` for `l ≠ l'`. -/
theorem PP_Fl_inter (l l' : Fin 4) (h : l ≠ l') :
    PP (Fl l ∩ Fl l') = ENNReal.ofReal (1 / 24) := by
  set pm := (Equiv.swap 3 l) * Equiv.swap 2 (Equiv.swap 3 l l')
  have : Fl l ∩ Fl l' =
      sp pm allTrue ⁻¹' {A | ‖A 0 + A 1 + A 2‖ < 1 ∧ ‖A 0 + A 1 + A 3‖ < 1} := by
    ext A
    simp only [Fl, mem_inter_iff, mem_preimage, mem_ofPred_eq, ← faceSum_three, ← faceSum_two,
      faceSum_perm, pm, swap_two l l' h, swap_three l l' h]
  rw [this, PP_sp, PP_F3F2]

/-! ## Generic position almost surely -/

lemma PP_sum3_null : PP {A | ‖A 0 + A 1 + A 2‖ = 1} = 0 := by
  have hS' : MeasurableSet {y : E3 × (E3 × E3) | ‖y.2.1 + y.2.2 + y.1‖ = 1} :=
    measurableSet_eq_fun (by fun_prop) measurable_const
  have : {A : Ω | ‖A 0 + A 1 + A 2‖ = 1} =
      Φ ⁻¹' (univ ×ˢ {y : E3 × (E3 × E3) | ‖y.2.1 + y.2.2 + y.1‖ = 1}) := by
    ext A; simp [Φ]
  rw [this, Φ_mp.measure_preimage (MeasurableSet.univ.prod hS').nullMeasurableSet,
    Measure.prod_prod, measure_univ, one_mul, Measure.prod_apply_symm hS',
    lintegral_prod_symm _ (measurable_measure_prodMk_right hS').aemeasurable]
  have hb : ∀ᵐ b ∂unif, ∫⁻ a, unif ((fun c => (c, (a, b))) ⁻¹'
      {y : E3 × (E3 × E3) | ‖y.2.1 + y.2.2 + y.1‖ = 1}) ∂unif = 0 := by
    filter_upwards [unif_ae_norm] with b hb
    have hnull : ∀ᵐ a ∂unif, inner ℝ a b ≠ -1 := by
      rw [ae_iff]; simpa using unif_eq_zero b hb (-1)
    rw [lintegral_congr_ae (g := fun _ => 0) ?_, lintegral_zero]
    filter_upwards [unif_ae_norm, hnull] with a ha hab
    change unif {c | ‖a + b + c‖ = 1} = 0
    have hv : a + b ≠ 0 := by
      intro h0
      apply hab
      rw [eq_neg_of_add_eq_zero_right h0, inner_neg_right, real_inner_self_eq_norm_sq, ha]
      norm_num
    refine measure_mono_null_ae ?_ (unif_eq_zero' (a + b) hv (-(‖a + b‖ ^ 2) / 2))
    filter_upwards [unif_ae_norm] with c hc hcs
    change ‖a + b + c‖ = 1 at hcs
    change inner ℝ c (a + b) = -(‖a + b‖ ^ 2) / 2
    have := norm_add_sq_real (a + b) c
    rw [hcs, hc, real_inner_comm] at this
    linarith
  rw [lintegral_congr_ae hb, lintegral_zero]

lemma cE_swap : ∀ e : Edge, ∀ m : Fin 4, cE e (Equiv.swap 3 e.1 m) =
    if m = 3 then 0 else sgZ (decide (cE e (Equiv.swap 3 e.1 m) = 1)) := by
  decide

lemma PP_edge_null (e : Edge) : PP {A | ‖vecOf A (cE e)‖ = 1} = 0 := by
  set pm := Equiv.swap 3 e.1
  set τ : Sign := fun m => decide (cE e (pm m) = 1)
  have : {A : Ω | ‖vecOf A (cE e)‖ = 1} = sp pm τ ⁻¹' {A | ‖A 0 + A 1 + A 2‖ = 1} := by
    ext A
    simp only [mem_ofPred_eq, mem_preimage, ← faceSum_three]
    congr! 2
    rw [vecOf, ← Equiv.sum_comp pm]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [sp_apply, cE_swap e m]
    split_ifs <;> simp [τ, pm]
  rw [this, PP_sp, PP_sum3_null]

/-- Almost surely the four points are unit vectors and no signed triple sum has norm `1`. -/
theorem ae_generic : ∀ᵐ A ∂PP, (∀ i, ‖A i‖ = 1) ∧ ∀ e, ‖vecOf A (cE e)‖ ≠ 1 := by
  refine (ae_all_iff.2 fun i => ?_).and (ae_all_iff.2 fun e => ?_)
  · exact (measurePreserving_eval (fun _ : Fin 4 => unif) i).quasiMeasurePreserving.ae
      unif_ae_norm
  · rw [ae_iff]; simpa using PP_edge_null e

/-! ## Flips -/

lemma acute_flip (A : Ω) (σ : Sign) :
    AcuteVariant A σ ↔ AcuteVariant (sp (Equiv.refl _) σ A) allTrue := by
  simp [AcuteVariant, P, sp_apply, allTrue, sgZ]

lemma faceSum_flip (A : Ω) (σ : Sign) (l : Fin 4) :
    faceSum A σ l = faceSum (sp (Equiv.refl _) σ A) allTrue l := by
  rw [faceSum_allTrue, faceSum, vecOf]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [sp_apply, cDrop]
  split_ifs <;> simp

lemma kShort_flip (A : Ω) (σ : Sign) :
    kShort A σ = kShort (sp (Equiv.refl _) σ A) allTrue := by
  simp only [kShort, faceSum_flip A σ]

/-! ## Measurability -/

lemma faceSum_cont (σ : Sign) (l : Fin 4) : Continuous fun A : Ω => faceSum A σ l := by
  unfold faceSum vecOf
  exact continuous_finsetSum _ fun i _ => by fun_prop

def Ac (σ : Sign) : Set Ω := {A | AcuteVariant A σ}

def Rs (σ : Sign) : Set Ω := {A | 1 ≤ kShort A σ ∧ kShort A σ ≤ 2}

lemma Ac_meas (σ : Sign) : MeasurableSet (Ac σ) := by
  simp only [Ac, AcuteVariant, ofPred_forall]
  refine MeasurableSet.iInter fun l => MeasurableSet.iInter fun k => ?_
  refine measurableSet_lt measurable_const (Continuous.measurable ?_)
  unfold P
  fun_prop

/-- Number of `true` entries of a pattern. -/
def cnt (f : Fin 4 → Bool) : ℕ := ((List.finRange 4).filter f).length

open Classical in
/-- Which face sums of `σ` are short. -/
noncomputable def pat (σ : Sign) (A : Ω) : Fin 4 → Bool := fun l => decide (‖faceSum A σ l‖ < 1)

lemma kShort_pat (A : Ω) (σ : Sign) : kShort A σ = cnt (pat σ A) := rfl

lemma pat_meas (σ : Sign) : Measurable (pat σ) := by
  refine measurable_pi_iff.2 fun l => measurable_to_bool ?_
  have : (fun A => pat σ A l) ⁻¹' {true} = {A | ‖faceSum A σ l‖ < 1} := by
    ext A; simp [pat]
  rw [this]
  exact measurableSet_lt ((faceSum_cont σ l).norm.measurable) measurable_const

lemma Rs_meas (σ : Sign) : MeasurableSet (Rs σ) := by
  have : Rs σ = pat σ ⁻¹' {f | 1 ≤ cnt f ∧ cnt f ≤ 2} := by
    ext A; simp [Rs, kShort_pat]
  rw [this]
  exact pat_meas σ (Set.toFinite _).measurableSet

lemma Fl_meas (l : Fin 4) : MeasurableSet (Fl l) :=
  measurableSet_lt ((faceSum_cont allTrue l).norm.measurable) measurable_const

/-! ## Integrating the count -/

lemma allSigns_card (p : Sign → Bool) :
    (allSigns.filter p).length = (Finset.univ.filter fun σ => p σ = true).card := by
  have hnd : allSigns.Nodup := by decide
  have hmem : ∀ σ, σ ∈ allSigns := by decide
  rw [← List.toFinset_card_of_nodup (hnd.filter p)]
  congr 1
  ext σ
  simp [hmem]

lemma indicator_sum (S : Sign → Set Ω) (A : Ω) [DecidablePred fun σ => A ∈ S σ] :
    ∑ σ, (S σ).indicator (1 : Ω → ENNReal) A = ((Finset.univ.filter fun σ => A ∈ S σ).card : ENNReal) := by
  simp [indicator_apply, Finset.sum_boole]

/-- **Lemma 4, integrated.** `16 P(T_∅ succeeds) + 16 P(1 ≤ k ≤ 2) = 8`. -/
theorem count_integrated : 16 * PP (Ac allTrue) + 16 * PP (Rs allTrue) = 8 := by
  classical
  have hpt : ∀ᵐ A ∂PP, ∑ σ, (Ac σ).indicator (1 : Ω → ENNReal) A +
      ∑ σ, (Rs σ).indicator (1 : Ω → ENNReal) A = 8 := by
    filter_upwards [ae_generic] with A hA
    have h := count_sixteen (V := E3) finrank_euclideanSpace_fin A hA.1 hA.2
    rw [allSigns_card, allSigns_card] at h
    rw [indicator_sum, indicator_sum]
    have h' : ((Finset.univ.filter fun σ => A ∈ Ac σ).card +
        (Finset.univ.filter fun σ => A ∈ Rs σ).card : ℕ) = 8 := by
      have e1 : (Finset.univ.filter fun σ => A ∈ Ac σ) =
          Finset.univ.filter fun σ => decide (AcuteVariant A σ) = true := by
        ext σ; rw [Finset.mem_filter, Finset.mem_filter]; simp [Ac]
      have e2 : (Finset.univ.filter fun σ => A ∈ Rs σ) =
          Finset.univ.filter fun σ => decide (1 ≤ kShort A σ ∧ kShort A σ ≤ 2) = true := by
        ext σ; rw [Finset.mem_filter, Finset.mem_filter]; simp [Rs]
      rw [e1, e2]; exact h
    exact_mod_cast h'
  have hint := lintegral_congr_ae hpt
  rw [lintegral_add_left (Finset.measurable_sum _ fun σ _ =>
      (measurable_one.indicator (Ac_meas σ))),
    lintegral_finsetSum _ (fun σ _ => measurable_one.indicator (Ac_meas σ)),
    lintegral_finsetSum _ (fun σ _ => measurable_one.indicator (Rs_meas σ)), lintegral_const,
    measure_univ, mul_one] at hint
  simp only [lintegral_indicator_one (Ac_meas _), lintegral_indicator_one (Rs_meas _)] at hint
  have hAc : ∀ σ, PP (Ac σ) = PP (Ac allTrue) := fun σ => by
    have : Ac σ = sp (Equiv.refl _) σ ⁻¹' Ac allTrue := by ext A; exact acute_flip A σ
    rw [this, PP_sp]
  have hRs : ∀ σ, PP (Rs σ) = PP (Rs allTrue) := fun σ => by
    have : Rs σ = sp (Equiv.refl _) σ ⁻¹' Rs allTrue := by
      ext A; simp only [Rs, mem_ofPred_eq, mem_preimage, kShort_flip A σ]
    rw [this, PP_sp]
  simp only [hAc, hRs, Finset.sum_const, Finset.card_univ] at hint
  simpa using hint

/-- The pairs `l < l'`. -/
def pairs6 : Finset (Fin 4 × Fin 4) := Finset.univ.filter fun p => p.1 < p.2

lemma pattern_identity : ∀ f : Fin 4 → Bool, cnt f ≤ 3 →
    (if 1 ≤ cnt f ∧ cnt f ≤ 2 then 1 else 0) +
      ∑ p ∈ pairs6, (if f p.1 = true ∧ f p.2 = true then 1 else 0) =
      ∑ l, (if f l = true then 1 else 0 : ℕ) := by
  decide

lemma pairs6_card : pairs6.card = 6 := by decide

/-- **Equation (5), integrated.** `P(1 ≤ k ≤ 2) + 6γ = 4α`. -/
theorem moments_integrated :
    PP (Rs allTrue) + 6 * ENNReal.ofReal (1 / 24) = 4 * ENNReal.ofReal (1 / 6) := by
  classical
  have hpt : ∀ᵐ A ∂PP, (Rs allTrue).indicator (1 : Ω → ENNReal) A +
      ∑ p ∈ pairs6, (Fl p.1 ∩ Fl p.2).indicator (1 : Ω → ENNReal) A =
      ∑ l, (Fl l).indicator (1 : Ω → ENNReal) A := by
    filter_upwards [ae_generic] with A hA
    have hk := (restrictions (V := E3) finrank_euclideanSpace_fin A hA.1 hA.2).2.1 allTrue
    rw [kShort_pat] at hk
    have h := pattern_identity (pat allTrue A) hk
    have hF : ∀ l, A ∈ Fl l ↔ pat allTrue A l = true := fun l => by simp [Fl, pat]
    have hR : A ∈ Rs allTrue ↔ 1 ≤ cnt (pat allTrue A) ∧ cnt (pat allTrue A) ≤ 2 := by
      simp [Rs, kShort_pat]
    simp only [indicator_apply, Pi.one_apply, mem_inter_iff, hF, hR]
    exact_mod_cast h
  have hint := lintegral_congr_ae hpt
  rw [lintegral_add_left (measurable_one.indicator (Rs_meas _)),
    lintegral_finsetSum _ (fun p _ => measurable_one.indicator ((Fl_meas _).inter (Fl_meas _))),
    lintegral_finsetSum _ (fun l _ => measurable_one.indicator (Fl_meas l))] at hint
  simp only [lintegral_indicator_one (Rs_meas _), lintegral_indicator_one (Fl_meas _),
    lintegral_indicator_one ((Fl_meas _).inter (Fl_meas _)), PP_Fl] at hint
  rw [Finset.sum_congr rfl (fun p hp => PP_Fl_inter p.1 p.2
    (by simp [pairs6] at hp; exact hp.ne))] at hint
  simpa [pairs6_card] using hint

/-! ## The theorem -/

/-- Every angle of every face of the tetrahedron `A 0 A 1 A 2 A 3` is acute. -/
def AllFacesAcute (A : Ω) : Prop :=
  ∀ i j k : Fin 4, i ≠ j → i ≠ k → j ≠ k → 0 < inner ℝ (A j - A i) (A k - A i)

lemma face_distinct : ∀ l : Fin 4, ∀ k : Fin 3,
    face l k ≠ face l (k + 1) ∧ face l k ≠ face l (k + 2) ∧ face l (k + 1) ≠ face l (k + 2) := by
  decide

lemma face_cover : ∀ i j k : Fin 4, i ≠ j → i ≠ k → j ≠ k → ∃ l : Fin 4, ∃ k' : Fin 3,
    face l k' = i ∧ ((face l (k' + 1) = j ∧ face l (k' + 2) = k) ∨
      (face l (k' + 1) = k ∧ face l (k' + 2) = j)) := by
  decide

lemma allFacesAcute_iff (A : Ω) : AllFacesAcute A ↔ A ∈ Ac allTrue := by
  have hP : ∀ i, P A allTrue i = A i := fun i => by simp [P, allTrue, sgZ]
  simp only [Ac, mem_ofPred_eq, AcuteVariant, hP]
  constructor
  · intro h l k
    obtain ⟨h1, h2, h3⟩ := face_distinct l k
    exact h _ _ _ h1 h2 h3
  · intro h i j k hij hik hjk
    obtain ⟨l, k', rfl, (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)⟩ := face_cover i j k hij hik hjk
    · exact h l k'
    · rw [real_inner_comm]; exact h l k'

/-- **Main theorem (MO 498296).** Four independent uniform points on the unit sphere form a
tetrahedron with four acute faces with probability exactly `1/12`. -/
theorem prob_all_faces_acute : PP {A | AllFacesAcute A} = ENNReal.ofReal (1 / 12) := by
  have hset : {A | AllFacesAcute A} = Ac allTrue := by
    ext A; exact allFacesAcute_iff A
  rw [hset]
  have h1 := count_integrated
  have h2 := moments_integrated
  have hp : PP (Ac allTrue) ≠ ⊤ := measure_ne_top _ _
  have hr : PP (Rs allTrue) ≠ ⊤ := measure_ne_top _ _
  have h1' := congrArg ENNReal.toReal h1
  have h2' := congrArg ENNReal.toReal h2
  rw [ENNReal.toReal_add (by finiteness) (by finiteness), ENNReal.toReal_mul,
    ENNReal.toReal_mul] at h1'
  rw [ENNReal.toReal_add hr (by finiteness), ENNReal.toReal_mul, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by norm_num), ENNReal.toReal_ofReal (by norm_num)] at h2'
  norm_num at h1' h2'
  rw [← ENNReal.ofReal_toReal hp]
  congr 1
  linarith

end AcuteTetra
