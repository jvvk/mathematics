import EnclosingCopy.Enclosing.SquareSegment
import EnclosingCopy.Enclosing.LPDual

/-!
# Classification of the optimum (Theorem 8, first step of the proof)

The event of the paper, in the model truncated at depth `T`: some optimal copy fits and its lines
stay below the cutoff (`OptFit`). This file proves the general tools:

* `badP_prob_zero`: Mecke null events for an extra point satisfying any measurable condition of
  Lebesgue-null sections (generalising `badExtra_prob_zero`);
* `optimum_kkt`: at an optimum of the model LP, `e₁` is a positive combination of linearly
  independent rows of tight points (`LPDual.lp_kkt`);
* `segCopy_of_tight`: a copy tight at the three points of a segment triple is one of their
  chord copies.
-/

namespace Enclosing
open MeasureTheory Set Matrix ENNReal

variable {m : ℕ} (K : Sides m)

/-! ### Null events for an extra point -/

section NullP

variable {k : ℕ} (P : (Fin k → Pt m) → Pt m → Prop)

/-- The last point satisfies `P` relative to the others. -/
def extraP (x : Fin (k + 1) → Pt m) : Prop :=
  P (fun r => x ((Fin.last k).succAbove r)) (x (Fin.last k))

/-- Some distinct sampled points satisfy `extraP`. -/
def BadP (ω : PoissonPP.Sample (Pt m)) : Prop :=
  ∃ i : Fin (k + 1) ↪ Fin ω.1, extraP P (ω.2 ∘ i)

variable {P} (hP : MeasurableSet {q : (Fin k → Pt m) × Pt m | P q.1 q.2})
include hP

lemma measurableSet_extraP : MeasurableSet {x : Fin (k + 1) → Pt m | extraP P x} := by
  have hfirst : Measurable (fun x : Fin (k + 1) → Pt m =>
      ((fun r => x (Fin.last k |>.succAbove r)), x (Fin.last k))) :=
    (Measurable.of_eval fun r => measurable_pi_apply _).prodMk (measurable_pi_apply _)
  exact hP.preimage hfirst

lemma measurableSet_BadP : MeasurableSet {ω : PoissonPP.Sample (Pt m) | BadP P ω} := by
  apply PoissonPP.measurableSet_sample
  intro n
  change MeasurableSet {y : Fin n → Pt m | ∃ i : Fin (k + 1) ↪ Fin n, extraP P (y ∘ i)}
  simp only [ofPred_exists]
  exact MeasurableSet.iUnion fun i => (measurableSet_extraP hP).preimage
    (Measurable.of_eval fun r => measurable_pi_apply (i r))

/-- **Null events for an extra point.** If every section `{p | P x p}` is `Λ`-null, then almost
surely no sampled point satisfies `P` relative to other sampled points. -/
theorem badP_prob_zero (T : ℝ) (hnull : ∀ x, Λ K T {p | P x p} = 0) :
    PoissonPP.law (Λ K T) {ω | BadP P ω} = 0 := by
  have hint : (∫⁻ x : Fin (k + 1) → Pt m,
      {x | extraP P x}.indicator (1 : (Fin (k + 1) → Pt m) → ℝ≥0∞) x
        ∂(Measure.pi fun _ => Λ K T)) = 0 := by
    let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k + 1) => Pt m) (Fin.last k)
    have he := measurePreserving_piFinSuccAbove (fun _ : Fin (k + 1) => Λ K T) (Fin.last k)
    change MeasurePreserving e _ _ at he
    let F : (Fin (k + 1) → Pt m) → ℝ≥0∞ := {x | extraP P x}.indicator 1
    have h := he.lintegral_comp_emb e.measurableEmbedding (fun q => F (e.symm q))
    simp only [e.symm_apply_apply] at h
    rw [h]
    have hM : Measurable (fun q => F (e.symm q)) :=
      (measurable_one.indicator (measurableSet_extraP hP)).comp e.symm.measurable
    rw [lintegral_prod_symm _ hM.aemeasurable]
    have inner : ∀ x : Fin k → Pt m, (∫⁻ p, F (e.symm (p, x)) ∂Λ K T) = 0 := by
      intro x
      have hf : (fun p : Pt m => F (e.symm (p, x))) = {p | P x p}.indicator 1 := by
        funext p
        have he1 : e (e.symm (p, x)) = (p, x) := e.apply_symm_apply _
        have hi : (e.symm (p, x)) (Fin.last k) = p := congrArg Prod.fst he1
        have hx : (fun r => (e.symm (p, x)) ((Fin.last k).succAbove r)) = x :=
          congrArg Prod.snd he1
        have hiff : P (fun r => (e.symm (p, x)) ((Fin.last k).succAbove r))
            ((e.symm (p, x)) (Fin.last k)) ↔ P x p := by rw [hx, hi]
        simp only [F, Set.indicator, mem_ofPred_eq, extraP, Pi.one_apply]
        by_cases hc : P x p
        · rw [if_pos (hiff.mpr hc), if_pos hc]
        · rw [if_neg (mt hiff.mp hc), if_neg hc]
      have hmeas : MeasurableSet {p | P x p} := measurable_prodMk_left hP
      rw [hf, lintegral_indicator_one hmeas, hnull x]
    simp_rw [inner]
    exact lintegral_zero
  have hcount : (∑' n : ℕ, PoissonPP.w0 (Λ K T) / n.factorial *
      ∫⁻ y : Fin n → Pt m, ∑ i : Fin (k + 1) ↪ Fin n,
        {x | extraP P x}.indicator (1 : (Fin (k + 1) → Pt m) → ℝ≥0∞) (y ∘ i)
        ∂(Measure.pi fun _ => Λ K T)) = 0 := by
    have h := PoissonPP.mecke (Λ K T) (k + 1)
      (fun x _ => {x | extraP P x}.indicator 1 x)
      (fun _ => (measurable_one.indicator (measurableSet_extraP hP)).comp measurable_fst)
    rw [h]
    simp only [PoissonPP.expect_const]
    exact hint
  have hbad := measurableSet_BadP hP
  rw [← lintegral_indicator_one hbad,
    PoissonPP.lintegral_law _ _ (measurable_one.indicator hbad)]
  apply le_antisymm _ bot_le
  change _ ≤ (0 : ℝ≥0∞)
  rw [← hcount]
  apply ENNReal.tsum_le_tsum
  intro n
  apply mul_le_mul le_rfl _ bot_le bot_le
  apply lintegral_mono
  intro y
  change {ω | BadP P ω}.indicator (1 : PoissonPP.Sample (Pt m) → ℝ≥0∞) ⟨n, y⟩ ≤
      ∑ i : Fin (k + 1) ↪ Fin n,
        {x | extraP P x}.indicator (1 : (Fin (k + 1) → Pt m) → ℝ≥0∞) (y ∘ i)
  by_cases hy : BadP P ⟨n, y⟩
  · rw [indicator_of_mem (show (⟨n, y⟩ : PoissonPP.Sample (Pt m)) ∈ {ω | BadP P ω} from hy),
      Pi.one_apply]
    obtain ⟨i, hi⟩ := hy
    have hsum := Finset.single_le_sum
      (s := Finset.univ) (f := fun j : Fin (k + 1) ↪ Fin n =>
        {x | extraP P x}.indicator (1 : (Fin (k + 1) → Pt m) → ℝ≥0∞) (y ∘ j))
      (fun _ _ => bot_le) (Finset.mem_univ i)
    rw [indicator_of_mem (show y ∘ i ∈ {x | extraP P x} from hi), Pi.one_apply] at hsum
    exact hsum
  · rw [indicator_of_notMem (show (⟨n, y⟩ : PoissonPP.Sample (Pt m)) ∉ {ω | BadP P ω} from hy)]
    exact bot_le

end NullP

/-- Points at a fixed position form a null set. -/
theorem intensity_position_zero (T c : ℝ) : Λ K T {p : Pt m | p.2.1 = c} = 0 := by
  have hm : MeasurableSet {p : Pt m | p.2.1 = c} :=
    measurableSet_eq_fun (measurable_fst.comp measurable_snd) measurable_const
  unfold Λ
  rw [Measure.coe_finsetSum, Finset.sum_apply]
  apply Finset.sum_eq_zero
  intro i _
  rw [Measure.dirac_prod, Measure.map_apply measurable_prodMk_left hm]
  apply le_antisymm _ bot_le
  calc (volume.restrict (Icc (K.a i) (K.b i) ×ˢ Icc (0 : ℝ) T)) (Prod.mk i ⁻¹' {p | p.2.1 = c})
      ≤ volume (Prod.mk i ⁻¹' {p : Pt m | p.2.1 = c}) := Measure.restrict_apply_le _ _
    _ ≤ volume ({c} ×ˢ (univ : Set ℝ)) := by
        apply measure_mono
        intro q hq
        exact ⟨hq, mem_univ _⟩
    _ = 0 := by rw [Measure.volume_eq_prod, Measure.prod_prod, measure_singleton, zero_mul]

/-! ### The event and the KKT condition -/

/-- **The event `E` in the model truncated at depth `T`**: some optimal copy fits, with its lines
below the cutoff. -/
def OptFit (T : ℝ) (ω : PoissonPP.Sample (Pt m)) : Prop :=
  ∃ z : Copy, Fits K z ∧ Below K T z ∧ Feasible K (PoissonPP.config ω.2) z ∧
    ∀ z', Feasible K (PoissonPP.config ω.2) z' → z.1 ≤ z'.1

/-- **KKT at an optimum of the model LP.** -/
theorem optimum_kkt {n : ℕ} (y : Fin n → Pt m) (z : Copy)
    (hz : Feasible K (PoissonPP.config y) z)
    (hopt : ∀ z', Feasible K (PoissonPP.config y) z' → z.1 ≤ z'.1) :
    ∃ t : Finset (Fin n), ∃ μ : Fin n → ℝ, (∀ i ∈ t, gx K z (y i) = 0) ∧ (∀ i ∈ t, 0 < μ i) ∧
      LinearIndependent ℝ (fun i : t => row K (y i)) ∧
      (Pi.single 0 1 : Fin 4 → ℝ) = ∑ i ∈ t, μ i • row K (y i) := by
  have hz' := (feasible_config_iff K y z).mp hz
  obtain ⟨t, μ, ht, hμ, hli, he⟩ := LPDual.lp_kkt (fun i => row K (y i)) (fun i => -(y i).2.2)
    (Pi.single 0 1) (zvec z)
    (fun i => by have := hz' i; rw [gx_eq] at this; linarith)
    (fun z' hz'' => by
      have hf : Feasible K (PoissonPP.config y) (copyOfVec z') := by
        rw [feasible_config_iff]
        intro i
        rw [gx_eq, zvec_copyOfVec]
        have := hz'' i
        linarith
      have h2 := hopt _ hf
      have h3 : (copyOfVec z').1 = z' 0 := rfl
      rw [h3] at h2
      simpa [single_dotProduct, zvec] using h2)
  refine ⟨t, μ, fun i hi => ?_, hμ, hli, he⟩
  rw [gx_eq, ht i hi]
  ring

/-- A copy tight at the three points of a segment triple is one of their chord copies. -/
theorem segCopy_of_tight {k kb : Fin m} (hP : ParPair K k kb) {x : Fin 3 → Pt m}
    (hx : SegGood k kb x) (z : Copy) (ht : ∀ r, gx K z (x r) = 0) :
    z = segCopy K k (segVec K k kb x) (dot z.2.1 (tang K k)) := by
  let v : Fin 3 → ℝ := ![z.1, dot z.2.1 (K.u k), z.2.2]
  have hu := hP.unit
  have hMv : segMat K k kb x *ᵥ v = fun r => -(x r).2.2 := by
    funext r
    have h := ht r
    have h0 := gx_segCopy hP hx v 0 r
    have hz : gx K z (x r) = gx K (segCopy K k v 0) (x r) := by
      match r with
      | 0 =>
        rw [gx_segCopy_k hP v 0 _ hx.1]
        simp only [gx, Hs, hx.1, v]
        simp [Matrix.cons_val_zero, Matrix.cons_val_one]; ring
      | 1 =>
        rw [gx_segCopy_k hP v 0 _ hx.2.1]
        simp only [gx, Hs, hx.2.1, v]
        simp [Matrix.cons_val_zero, Matrix.cons_val_one]; ring
      | 2 =>
        rw [gx_segCopy_kb hP v 0 _ hx.2.2.1]
        simp only [gx, Hs, hx.2.2.1, v, hP.par]
        simp [dot, Matrix.cons_val_zero, Matrix.cons_val_one]; ring
    rw [hz, h0] at h
    linarith
  have hv : segVec K k kb x = v := by
    rw [segVec, ← hMv, Matrix.mulVec_mulVec,
      Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (segMat_det_ne hP hx)), Matrix.one_mulVec]
  rw [hv]
  obtain ⟨ε, ⟨C1, C2⟩, Θ⟩ := z
  simp only [segCopy, chordCopy, tang, dot, v, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Prod.mk.injEq, true_and, and_true]
  refine ⟨?_, ?_⟩
  · first | linear_combination C1 * hu | linear_combination (-C1) * hu
  · first | linear_combination C2 * hu | linear_combination (-C2) * hu

/-! ### The square: the support of the KKT multipliers -/

lemma square_h (j : Fin 4) : squareSides.h j = 1 / 2 := rfl

lemma square_u_add_two (j : Fin 4) : squareSides.u (j + 2) = -squareSides.u j := by
  fin_cases j <;> simp [squareSides] <;> rfl

lemma fin4_add_two_add_two (j : Fin 4) : j + 2 + 2 = j := by fin_cases j <;> rfl

lemma fin4_add_two_ne (j : Fin 4) : j + 2 ≠ j := by fin_cases j <;> decide

lemma fin4_cases (j s : Fin 4) (h1 : s ≠ j) (h2 : s ≠ j + 2) : s = j + 1 ∨ s = j + 1 + 2 := by
  fin_cases j <;> fin_cases s <;> simp_all <;> decide

lemma row_square (q : Pt 4) :
    row squareSides q = ![1 / 2, (squareSides.u q.1).1, (squareSides.u q.1).2, -q.2.1] := rfl

lemma row0 (q : Pt 4) : row squareSides q 0 = 1 / 2 := rfl
lemma row1 (q : Pt 4) : row squareSides q 1 = (squareSides.u q.1).1 := rfl
lemma row2 (q : Pt 4) : row squareSides q 2 = (squareSides.u q.1).2 := rfl
lemma row3 (q : Pt 4) : row squareSides q 3 = -q.2.1 := rfl

section Support

variable {ι : Type*} [DecidableEq ι] (p : ι → Pt 4) (t : Finset ι) (μ : ι → ℝ)

/-- Points of `t` on side `j`. -/
def onSide (j : Fin 4) : Finset ι := t.filter fun i => (p i).1 = j

/-- Multiplier mass on side `j`. -/
noncomputable def mass (j : Fin 4) : ℝ := ∑ i ∈ onSide p t j, μ i

variable {p t μ}

lemma sum_by_side (f : Fin 4 → ℝ) :
    ∑ i ∈ t, μ i * f (p i).1 = ∑ j, f j * mass p t μ j := by
  rw [← Finset.sum_fiberwise t (fun i => (p i).1)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mass, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [(Finset.mem_filter.mp hi).2]; ring

lemma li_comp3 (hli : LinearIndependent ℝ (fun i : t => row squareSides (p i)))
    {a b c : ι} (ha : a ∈ t) (hb : b ∈ t) (hc : c ∈ t) (hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c) : LinearIndependent ℝ (fun r : Fin 3 => row squareSides (p (![a, b, c] r))) := by
  let f : Fin 3 → t := fun r => ⟨![a, b, c] r, by fin_cases r <;> simpa⟩
  have hf : Function.Injective f := by
    intro r r' h
    have h' := congrArg Subtype.val h
    fin_cases r <;> fin_cases r' <;> simp_all [f] <;> simp_all [eq_comm]
  exact hli.comp f hf

lemma li_comp4 (hli : LinearIndependent ℝ (fun i : t => row squareSides (p i)))
    {a b c d : ι} (ha : a ∈ t) (hb : b ∈ t) (hc : c ∈ t) (hd : d ∈ t) (hab : a ≠ b)
    (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    LinearIndependent ℝ (fun r : Fin 4 => row squareSides (p (![a, b, c, d] r))) := by
  let f : Fin 4 → t := fun r => ⟨![a, b, c, d] r, by fin_cases r <;> simpa⟩
  have hf : Function.Injective f := by
    intro r r' h
    have h' := congrArg Subtype.val h
    fin_cases r <;> fin_cases r' <;> simp_all [f] <;> simp_all [eq_comm]
  exact hli.comp f hf

/-- Distinct points of the support on the same side have distinct positions. -/
lemma pos_ne (hli : LinearIndependent ℝ (fun i : t => row squareSides (p i))) {a b : ι}
    (ha : a ∈ t) (hb : b ∈ t) (hab : a ≠ b) (hs : (p a).1 = (p b).1) : (p a).2.1 ≠ (p b).2.1 := by
  intro he
  have h := hli.injective (a₁ := ⟨a, ha⟩) (a₂ := ⟨b, hb⟩) (by simp [row_square, hs, he])
  exact hab (congrArg Subtype.val h)

/-- At most two support points on a side. -/
lemma card_onSide_le (hli : LinearIndependent ℝ (fun i : t => row squareSides (p i))) (j : Fin 4) :
    (onSide p t j).card ≤ 2 := by
  by_contra h
  obtain ⟨a, b, c, ha, hb, hc, hab, hac, hbc⟩ := (Finset.two_lt_card_iff (s := onSide p t j)).mp (by omega)
  have ha' := Finset.mem_filter.mp ha
  have hb' := Finset.mem_filter.mp hb
  have hc' := Finset.mem_filter.mp hc
  have h3 := li_comp3 hli ha'.1 hb'.1 hc'.1 hab hac hbc
  have hz := Fintype.linearIndependent_iff.mp h3
    ![(p b).2.1 - (p c).2.1, (p c).2.1 - (p a).2.1, (p a).2.1 - (p b).2.1] (by
      funext q
      simp only [Fin.sum_univ_three, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply,
        row_square]
      fin_cases q <;> simp [ha'.2, hb'.2, hc'.2] <;> ring) 0
  simp at hz
  exact pos_ne hli hb'.1 hc'.1 hbc (hb'.2.trans hc'.2.symm) (by linarith)

/-- Not two support points on each of two opposite sides. -/
lemma not_two_two (hli : LinearIndependent ℝ (fun i : t => row squareSides (p i))) (j : Fin 4)
    (h1 : 1 < (onSide p t j).card) (h2 : 1 < (onSide p t (j + 2)).card) : False := by
  obtain ⟨a, b, ha, hb, hab⟩ := Finset.one_lt_card_iff.mp h1
  obtain ⟨c, d, hc, hd, hcd⟩ := Finset.one_lt_card_iff.mp h2
  have ha' := Finset.mem_filter.mp ha
  have hb' := Finset.mem_filter.mp hb
  have hc' := Finset.mem_filter.mp hc
  have hd' := Finset.mem_filter.mp hd
  have hne : ∀ {x y : ι}, (p x).1 = j → (p y).1 = j + 2 → x ≠ y := by
    intro x y hx hy hxy; rw [hxy, hy] at hx; exact fin4_add_two_ne j hx
  have h4 := li_comp4 hli ha'.1 hb'.1 hc'.1 hd'.1 hab (hne ha'.2 hc'.2) (hne ha'.2 hd'.2)
    (hne hb'.2 hc'.2) (hne hb'.2 hd'.2) hcd
  have hu := square_u_add_two j
  have hz := Fintype.linearIndependent_iff.mp h4
    ![(p c).2.1 - (p d).2.1, -((p c).2.1 - (p d).2.1), -((p a).2.1 - (p b).2.1),
      (p a).2.1 - (p b).2.1] (by
      funext q
      simp only [Fin.sum_univ_four, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply,
        row_square]
      fin_cases q <;> simp [ha'.2, hb'.2, hc'.2, hd'.2, hu] <;> ring) 0
  simp at hz
  exact pos_ne hli hc'.1 hd'.1 hcd (hc'.2.trans hd'.2.symm) (by linarith)

variable (hμ : ∀ i ∈ t, 0 < μ i)
include hμ

lemma mass_pos_iff (j : Fin 4) : 0 < mass p t μ j ↔ (onSide p t j).Nonempty := by
  constructor
  · intro h
    by_contra hne
    rw [Finset.not_nonempty_iff_eq_empty] at hne
    simp [mass, hne] at h
  · intro hne
    exact Finset.sum_pos (fun i hi => hμ i (Finset.mem_filter.mp hi).1) hne

/-- **The support of the KKT multipliers for the square.** -/
theorem square_support (hli : LinearIndependent ℝ (fun i : t => row squareSides (p i)))
    (he : (Pi.single 0 1 : Fin 4 → ℝ) = ∑ i ∈ t, μ i • row squareSides (p i)) :
    (∀ j, (onSide p t j).card = 1) ∨
    (∃ j : Fin 4, ∃ a b c : ι, t = {a, b, c} ∧ a ≠ b ∧ (p a).1 = j ∧ (p b).1 = j ∧
      (p c).1 = j + 2 ∧ (p a).2.1 < (p b).2.1 ∧ 0 < μ a ∧ 0 < μ b ∧ 0 < μ c ∧
      μ a + μ b = μ c ∧ (μ a + μ b) * (squareSides.h j + squareSides.h (j + 2)) = 1 ∧
      μ a * (p a).2.1 + μ b * (p b).2.1 + μ c * (p c).2.1 = 0) ∨
    (∃ a ∈ t, ∃ b ∈ t, (p b).1 = (p a).1 + 2 ∧ (p a).2.1 + (p b).2.1 = 0) := by
  -- the four coordinates of the KKT identity
  have hc : ∀ q : Fin 4, (Pi.single 0 1 : Fin 4 → ℝ) q =
      ∑ i ∈ t, μ i * row squareSides (p i) q := by
    intro q
    rw [he, Finset.sum_apply]
    rfl
  have e0 : ∑ i ∈ t, μ i = 2 := by
    have := hc 0
    simp only [row0, Pi.single_eq_same] at this
    rw [← Finset.sum_mul] at this
    linarith
  have e1 : mass p t μ 0 = mass p t μ 2 := by
    have := hc 1
    simp only [row1] at this
    rw [sum_by_side (fun j => (squareSides.u j).1), Fin.sum_univ_four] at this
    simp [squareSides, Pi.single_apply] at this
    linarith
  have e2 : mass p t μ 1 = mass p t μ 3 := by
    have := hc 2
    simp only [row2] at this
    rw [sum_by_side (fun j => (squareSides.u j).2), Fin.sum_univ_four] at this
    simp [squareSides, Pi.single_apply] at this
    linarith
  have e3 : ∑ i ∈ t, μ i * (p i).2.1 = 0 := by
    have := hc 3
    simp only [row3, mul_neg, Finset.sum_neg_distrib] at this
    simp [Pi.single_apply] at this
    linarith
  have emass : ∀ j, mass p t μ (j + 2) = mass p t μ j := by
    intro j; fin_cases j <;> simp [e1, e2] <;> first | rfl | linarith | skip
  have etot : ∑ j, mass p t μ j = 2 := by
    rw [← e0]
    have := sum_by_side (p := p) (t := t) (μ := μ) (fun _ => (1 : ℝ))
    simp only [mul_one, one_mul] at this
    exact this.symm
  have hcard : t.card = ∑ j, (onSide p t j).card :=
    Finset.card_eq_sum_card_fiberwise (fun i _ => Finset.mem_univ _)
  have hle4 : t.card ≤ 4 := by
    have := hli.fintype_card_le_finrank
    simpa using this
  by_cases hall : ∀ j, (onSide p t j).Nonempty
  · left
    have h1 : ∀ j, 1 ≤ (onSide p t j).card := fun j => Finset.card_pos.mpr (hall j)
    rw [Fin.sum_univ_four] at hcard
    intro j
    have := h1 0; have := h1 1; have := h1 2; have := h1 3
    fin_cases j <;> simp <;> omega
  right
  push Not at hall
  obtain ⟨j, hj⟩ := hall
  have hmj : mass p t μ j = 0 := by simp [mass, hj]
  have hj2 : onSide p t (j + 2) = ∅ := by
    rw [← Finset.not_nonempty_iff_eq_empty, ← mass_pos_iff hμ, emass, hmj]
    exact lt_irrefl 0
  set i := j + 1 with hi
  -- every support point is on side `i` or `i + 2`
  have hside : ∀ x ∈ t, (p x).1 = i ∨ (p x).1 = i + 2 := by
    intro x hx
    apply fin4_cases j
    · intro h; have : x ∈ onSide p t j := Finset.mem_filter.mpr ⟨hx, h⟩; simp [hj] at this
    · intro h; have : x ∈ onSide p t (j + 2) := Finset.mem_filter.mpr ⟨hx, h⟩; simp [hj2] at this
  have ht : t = onSide p t i ∪ onSide p t (i + 2) := by
    ext x
    simp only [Finset.mem_union, onSide, Finset.mem_filter]
    constructor
    · intro hx; rcases hside x hx with h | h <;> simp [hx, h]
    · rintro (⟨hx, -⟩ | ⟨hx, -⟩) <;> exact hx
  have hdisj : Disjoint (onSide p t i) (onSide p t (i + 2)) := by
    rw [Finset.disjoint_left]
    intro x hx hx2
    have h1 := (Finset.mem_filter.mp hx).2
    have h2 := (Finset.mem_filter.mp hx2).2
    rw [h1] at h2; exact fin4_add_two_ne i h2.symm
  have hmi : mass p t μ i + mass p t μ (i + 2) = 2 := by
    have h := Finset.sum_union (f := μ) hdisj
    rw [← ht, e0] at h
    simp only [mass]; linarith
  have hm1 : mass p t μ i = 1 := by have := emass i; linarith
  have hne1 : (onSide p t i).Nonempty := (mass_pos_iff hμ i).mp (by linarith)
  have hne2 : (onSide p t (i + 2)).Nonempty :=
    (mass_pos_iff hμ (i + 2)).mp (by rw [emass]; linarith)
  have hw : ∀ j', squareSides.h j' + squareSides.h (j' + 2) = 1 := by
    intro j'; simp only [square_h]; norm_num
  -- two points on one side and one on the opposite side: a segment
  have segcase : ∀ (j' : Fin 4) (a b c : ι), a ≠ b → onSide p t j' = {a, b} →
      onSide p t (j' + 2) = {c} → t = {a, b, c} → mass p t μ j' = mass p t μ (j' + 2) →
      mass p t μ j' = 1 →
      ∃ j : Fin 4, ∃ a b c : ι, t = {a, b, c} ∧ a ≠ b ∧ (p a).1 = j ∧ (p b).1 = j ∧
        (p c).1 = j + 2 ∧ (p a).2.1 < (p b).2.1 ∧ 0 < μ a ∧ 0 < μ b ∧ 0 < μ c ∧
        μ a + μ b = μ c ∧ (μ a + μ b) * (squareSides.h j + squareSides.h (j + 2)) = 1 ∧
        μ a * (p a).2.1 + μ b * (p b).2.1 + μ c * (p c).2.1 = 0 := by
    intro j' a b c hab hS hS2 htt hmeq hm
    obtain ⟨hat, has⟩ := Finset.mem_filter.mp (show a ∈ onSide p t j' by rw [hS]; simp)
    obtain ⟨hbt, hbs⟩ := Finset.mem_filter.mp (show b ∈ onSide p t j' by rw [hS]; simp)
    obtain ⟨hct, hcs⟩ := Finset.mem_filter.mp (show c ∈ onSide p t (j' + 2) by rw [hS2]; simp)
    have hac : a ≠ c := by
      intro h; rw [h, hcs] at has; exact fin4_add_two_ne j' has
    have hbc : b ≠ c := by
      intro h; rw [h, hcs] at hbs; exact fin4_add_two_ne j' hbs
    have hma : mass p t μ j' = μ a + μ b := by rw [mass, hS, Finset.sum_pair hab]
    have hmc : mass p t μ (j' + 2) = μ c := by rw [mass, hS2, Finset.sum_singleton]
    have hs3 : μ a * (p a).2.1 + μ b * (p b).2.1 + μ c * (p c).2.1 = 0 := by
      rw [← e3, htt, Finset.sum_insert (by simp [hab, hac]), Finset.sum_insert (by simp [hbc]),
        Finset.sum_singleton]
      ring
    rcases lt_or_gt_of_ne (pos_ne hli hat hbt hab (has.trans hbs.symm)) with hlt | hgt
    · exact ⟨j', a, b, c, htt, hab, has, hbs, hcs, hlt, hμ a hat, hμ b hbt, hμ c hct,
        by linarith, by rw [hw]; linarith, hs3⟩
    · exact ⟨j', b, a, c, by rw [htt, Finset.insert_comm], hab.symm, hbs, has, hcs, hgt,
        hμ b hbt, hμ a hat, hμ c hct, by linarith, by rw [hw]; linarith, by linarith⟩
  have hc1 := card_onSide_le hli i
  have hc2 := card_onSide_le hli (i + 2)
  have hp1 := Finset.card_pos.mpr hne1
  have hp2 := Finset.card_pos.mpr hne2
  rcases (by omega : (onSide p t i).card = 1 ∨ (onSide p t i).card = 2) with h1 | h1 <;>
    rcases (by omega : (onSide p t (i + 2)).card = 1 ∨ (onSide p t (i + 2)).card = 2) with
      h2 | h2
  · -- one point on each of two opposite sides: a null event
    right
    obtain ⟨a, hS⟩ := Finset.card_eq_one.mp h1
    obtain ⟨b, hS2⟩ := Finset.card_eq_one.mp h2
    obtain ⟨hat, has⟩ := Finset.mem_filter.mp (show a ∈ onSide p t i by rw [hS]; simp)
    obtain ⟨hbt, hbs⟩ := Finset.mem_filter.mp (show b ∈ onSide p t (i + 2) by rw [hS2]; simp)
    have hab : a ≠ b := by intro h; rw [h, hbs] at has; exact fin4_add_two_ne i has
    have hma : mass p t μ i = μ a := by rw [mass, hS, Finset.sum_singleton]
    have hmb : mass p t μ (i + 2) = μ b := by rw [mass, hS2, Finset.sum_singleton]
    have htt : t = {a, b} := by rw [hS, hS2] at ht; rw [ht]; rfl
    have hs : μ a * (p a).2.1 + μ b * (p b).2.1 = 0 := by
      rw [← e3, htt, Finset.sum_pair hab]
    have hμab : μ a = μ b := by rw [← hma, ← hmb, emass]
    refine ⟨a, hat, b, hbt, by rw [has, hbs], ?_⟩
    rw [← hμab] at hs
    have := hμ a hat
    have : μ a * ((p a).2.1 + (p b).2.1) = 0 := by linarith
    rcases mul_eq_zero.mp this with h | h
    · linarith
    · exact h
  · -- one on side `i`, two on side `i + 2`
    left
    obtain ⟨c, hS⟩ := Finset.card_eq_one.mp h1
    obtain ⟨a, b, hab, hS2⟩ := Finset.card_eq_two.mp h2
    have htt : t = {a, b, c} := by
      rw [hS, hS2] at ht; rw [ht]; ext x; simp only [Finset.mem_union, Finset.mem_insert,
        Finset.mem_singleton]; tauto
    exact segcase (i + 2) a b c hab hS2 (by rw [fin4_add_two_add_two]; exact hS) htt
      (by rw [fin4_add_two_add_two, emass]) (by rw [emass]; exact hm1)
  · -- two on side `i`, one on side `i + 2`
    left
    obtain ⟨a, b, hab, hS⟩ := Finset.card_eq_two.mp h1
    obtain ⟨c, hS2⟩ := Finset.card_eq_one.mp h2
    have htt : t = {a, b, c} := by
      rw [hS, hS2] at ht; rw [ht]; ext x; simp only [Finset.mem_union, Finset.mem_insert,
        Finset.mem_singleton]; tauto
    exact segcase i a b c hab hS hS2 htt (emass i).symm hm1
  · exact (not_two_two hli i (by omega) (by omega)).elim

end Support

/-! ### The square: every fitting optimum is a candidate, almost surely -/

/-- Two sampled points on opposite sides of the square at opposite positions. -/
def OppP (x : Fin 1 → Pt 4) (q : Pt 4) : Prop := q.1 = (x 0).1 + 2 ∧ (x 0).2.1 + q.2.1 = 0

lemma measurableSet_OppP : MeasurableSet {q : (Fin 1 → Pt 4) × Pt 4 | OppP q.1 q.2} := by
  have h1 : Measurable fun q : (Fin 1 → Pt 4) × Pt 4 => q.2.1 := measurable_fst.comp measurable_snd
  have h2 : Measurable fun q : (Fin 1 → Pt 4) × Pt 4 => (q.1 0).1 + 2 :=
    (measurable_of_countable (fun j : Fin 4 => j + 2)).comp
      (measurable_fst.comp ((measurable_pi_apply 0).comp measurable_fst))
  have h3 : Measurable fun q : (Fin 1 → Pt 4) × Pt 4 => (q.1 0).2.1 + q.2.2.1 :=
    ((measurable_fst.comp measurable_snd).comp ((measurable_pi_apply 0).comp measurable_fst)).add
      ((measurable_fst.comp measurable_snd).comp measurable_snd)
  exact (measurableSet_eq_fun h1 h2).inter (measurableSet_eq_fun h3 measurable_const)

/-- The null event of two opposite points at opposite positions. -/
theorem opp_null (T : ℝ) : PoissonPP.law (Λ squareSides T) {ω | BadP OppP ω} = 0 :=
  badP_prob_zero squareSides measurableSet_OppP T fun x =>
    measure_mono_null (fun q (hq : OppP x q) => (show q.2.1 = -(x 0).2.1 by linarith [hq.2]))
      (intensity_position_zero squareSides T _)

lemma badP_of_opp {n : ℕ} (y : Fin n → Pt 4) {a b : Fin n} (hab : a ≠ b)
    (h : OppP (fun _ => y a) (y b)) : BadP OppP ⟨n, y⟩ := by
  refine ⟨⟨![a, b], fun r r' hr => ?_⟩, ?_⟩
  · fin_cases r <;> fin_cases r' <;> simp_all [eq_comm]
  · exact h

/-- **Classification of fitting optima for the square.** If some optimal copy fits (below the
cutoff), then there is a certified vertex candidate, or a segment candidate on one of the four
ordered pairs of parallel sides, or two sampled points lie on opposite sides at opposite
positions (a null event). -/
theorem square_classify (T : ℝ) (ω : PoissonPP.Sample (Pt 4)) (h : OptFit squareSides T ω) :
    HasVertexCandidate squareSides T ω ∨ (∃ k : Fin 4, HasSegCand squareSides k (k + 2) T ω) ∨
      BadP OppP ω := by
  classical
  obtain ⟨n, y⟩ := ω
  obtain ⟨z, hF, hB, hfeas, hopt⟩ := h
  obtain ⟨t, μ, ht, hμ, hli, he⟩ := optimum_kkt squareSides y z hfeas hopt
  rcases square_support hμ hli he with hV | hS | hN
  · -- one tight point on each side: a vertex candidate
    left
    have hex : ∀ r : Fin 4, ∃ a, onSide y t r = {a} := fun r => Finset.card_eq_one.mp (hV r)
    choose a ha using hex
    have hmem : ∀ r, a r ∈ t ∧ (y (a r)).1 = r := fun r =>
      Finset.mem_filter.mp (show a r ∈ onSide y t r by rw [ha r]; simp)
    have hinj : Function.Injective a := fun r r' h => by
      rw [← (hmem r).2, ← (hmem r').2, h]
    let f : Fin 4 ↪ Fin n := ⟨a, hinj⟩
    have htim : t = Finset.univ.map f := by
      ext x
      constructor
      · intro hx
        have hxs : x ∈ onSide y t (y x).1 := Finset.mem_filter.mpr ⟨hx, rfl⟩
        rw [ha, Finset.mem_singleton] at hxs
        exact Finset.mem_map.mpr ⟨(y x).1, Finset.mem_univ _, hxs.symm⟩
      · intro hx
        obtain ⟨r, -, rfl⟩ := Finset.mem_map.mp hx
        exact (hmem r).1
    have hli4 : LinearIndependent ℝ (fun r => row squareSides (y (a r))) :=
      hli.comp (fun r => ⟨a r, (hmem r).1⟩) fun r r' h => hinj (congrArg Subtype.val h)
    have hA : (vertexMatrix squareSides (y ∘ f)).det ≠ 0 := by
      have hu : IsUnit (vertexMatrix squareSides (y ∘ f)) :=
        Matrix.linearIndependent_rows_iff_isUnit.mp hli4
      exact ((Matrix.isUnit_iff_isUnit_det _).mp hu).ne_zero
    have hcert : ∀ c, ∑ r, μ (a r) * row squareSides ((y ∘ f) r) c =
        if c = 0 then 1 else 0 := by
      intro c
      have h1 := congrFun he c
      rw [htim, Finset.sum_map, Finset.sum_apply] at h1
      simp only [Pi.smul_apply, smul_eq_mul, Pi.single_apply] at h1
      exact h1.symm
    have hc := vertexCert_eq_of_certificate squareSides (y ∘ f) hA _ hcert
    have hz := vertexCopy_eq_of_tight squareSides (y ∘ f) hA z fun r => ht _ (hmem r).1
    refine ⟨f, ⟨hA, ?_, ?_, ?_⟩, ?_⟩
    · rw [hc]; exact fun r => hμ _ (hmem r).1
    · rw [hz]; exact hF
    · rw [hz]; exact hB
    · rw [hz]; exact hfeas
  · -- two tight points on a side and one on the opposite side: a segment candidate
    right; left
    obtain ⟨j, a, b, c, htt, hab, hsa, hsb, hsc, hlt, hμa, hμb, hμc, hsum, hw, hs⟩ := hS
    have hac : a ≠ c := by intro h; rw [h, hsc] at hsa; exact fin4_add_two_ne j hsa
    have hbc : b ≠ c := by intro h; rw [h, hsc] at hsb; exact fin4_add_two_ne j hsb
    let g : Fin 3 ↪ Fin n := ⟨![a, b, c], fun r r' hr => by
      fin_cases r <;> fin_cases r' <;> simp_all [eq_comm]⟩
    have hg : SegGood j (j + 2) (y ∘ g) :=
      ⟨hsa, hsb, hsc, (kkt_segment_iff (s₃ := (y c).2.1) hlt (by simp only [square_h]; norm_num)).mp
        ⟨μ a, μ b, μ c, hμa, hμb, hμc, hsum, hw, hs⟩⟩
    have htight : ∀ r, gx squareSides z ((y ∘ g) r) = 0 := by
      intro r
      fin_cases r
      · exact ht a (by rw [htt]; simp)
      · exact ht b (by rw [htt]; simp)
      · exact ht c (by rw [htt]; simp)
    have hz := segCopy_of_tight squareSides (squarePair j) hg z htight
    refine ⟨j, g, hg, dot z.2.1 (tang squareSides j), ⟨?_, ?_⟩, ?_⟩
    · rw [← hz]; exact hF
    · rw [← hz]; exact hB
    · rw [← hz]; exact hfeas
  · -- a null event
    right; right
    obtain ⟨a, -, b, -, hside, hpos⟩ := hN
    have hab : a ≠ b := by
      intro h; rw [h] at hside; exact fin4_add_two_ne _ hside.symm
    exact badP_of_opp y hab ⟨hside, hpos⟩

/-! ### Candidates are fitting optima -/

lemma optFit_of_vertex (T : ℝ) (ω : PoissonPP.Sample (Pt m))
    (h : HasVertexCandidate K T ω) : OptFit K T ω := by
  obtain ⟨z, hF, hB, hf, hopt⟩ := vertex_candidate_unique_optimum K T ω h
  exact ⟨z, hF, hB, hf, fun z' hz' => (hopt z' hz').1⟩

lemma optFit_of_seg {k kb : Fin m} (hP : ParPair K k kb) (T : ℝ) (ω : PoissonPP.Sample (Pt m))
    (h : HasSegCand K k kb T ω) : OptFit K T ω := by
  obtain ⟨i, hg, c, ⟨hF, hB⟩, hf⟩ := h
  refine ⟨_, hF, hB, hf, fun z' hz' => ?_⟩
  rw [segCopy_fst]
  exact (seg_optimal hP hg z' fun r => (feasible_config_iff K _ z').mp hz' (i r)).1

/-! ### The square: the candidate events overlap only on null events -/

lemma fin4_succ_ne (k : Fin 4) : k + 1 ≠ k := by fin_cases k <;> decide
lemma fin4_succ_ne_two (k : Fin 4) : k + 1 ≠ k + 2 := by fin_cases k <;> decide
lemma fin4_succ_two (k : Fin 4) : k + 1 + 2 = k + 3 := by fin_cases k <;> rfl
lemma fin4_three_succ (k : Fin 4) : k + 3 + 1 = k := by fin_cases k <;> rfl
lemma fin4_three_succ_two (k : Fin 4) : k + 3 + 1 + 2 = k + 2 := by fin_cases k <;> rfl

/-- Three segment points and a point on a perpendicular side have an invertible tight matrix. -/
lemma perp_rows_det (k : Fin 4) (q : Fin 4 → Pt 4) (h0 : (q 0).1 = k) (h1 : (q 1).1 = k)
    (h2 : (q 2).1 = k + 2) (h3 : (q 3).1 = k + 1) (hs : (q 0).2.1 ≠ (q 1).2.1) :
    (vertexMatrix squareSides q).det ≠ 0 := by
  have hli : LinearIndependent ℝ (vertexMatrix squareSides q).row := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have e : ∀ c, ∑ r, g r * row squareSides (q r) c = 0 := fun c => by
      have := congrFun hg c
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this
      exact this
    have c0 := e 0
    have c1 := e 1
    have c2 := e 2
    have c3 := e 3
    simp only [Fin.sum_univ_four, row0, row1, row2, row3, h0, h1, h2, h3] at c0 c1 c2 c3
    have hfin : g 3 = 0 ∧ g 2 = 0 ∧ g 1 = -g 0 := by
      fin_cases k <;> simp [squareSides] at c0 c1 c2 <;> refine ⟨?_, ?_, ?_⟩ <;> linarith
    obtain ⟨g3, g2, g10⟩ := hfin
    have hm : g 0 * ((q 0).2.1 - (q 1).2.1) = 0 := by
      rw [g3, g2, g10] at c3; linarith
    have g0 : g 0 = 0 := (mul_eq_zero.mp hm).resolve_right (sub_ne_zero.mpr hs)
    intro r
    fin_cases r <;> simp [g0, g2, g3, g10]
  exact ((Matrix.isUnit_iff_isUnit_det _).mp
    (Matrix.linearIndependent_rows_iff_isUnit.mp hli)).ne_zero

/-- A certified vertex candidate and a segment candidate: only on null events. -/
lemma vertex_seg_null (T : ℝ) (k : Fin 4) (ω : PoissonPP.Sample (Pt 4))
    (hV : HasVertexCandidate squareSides T ω) (hS : HasSegCand squareSides k (k + 2) T ω) :
    BadExtra squareSides (vertexCopy squareSides) ω ∨ BadP OppP ω := by
  classical
  obtain ⟨n, y⟩ := ω
  by_cases hbad : BadExtra squareSides (vertexCopy squareSides) ⟨n, y⟩
  · exact Or.inl hbad
  right
  obtain ⟨i, hgV, hfV⟩ := hV
  obtain ⟨j, hg, c, -, hfS⟩ := hS
  have hP := squarePair k
  have hfV' := (feasible_config_iff squareSides y _).mp hfV
  have hfS' := (feasible_config_iff squareSides y _).mp hfS
  have h1 := vertexGood_optimal squareSides T _ hgV _ fun r => hfS' (i r)
  have h2 := (seg_optimal hP hg (vertexCopy squareSides (y ∘ i)) fun r => hfV' (j r)).1
  have heq := vertexGood_unique squareSides T _ hgV _ (fun r => hfS' (i r))
    (le_antisymm h2 h1)
  -- the segment points are among the vertex points
  have hin : ∀ r, ∃ r', i r' = j r := by
    intro r
    have ht : gx squareSides (vertexCopy squareSides (y ∘ i)) (y (j r)) = 0 := by
      rw [← heq]; exact segCopy_tight hP hg c r
    exact tight_index_in_range squareSides y hbad i (j r) ht
  obtain ⟨r0, hr0⟩ := hin 0
  obtain ⟨r1, hr1⟩ := hin 1
  have hr01 : r0 ≠ r1 := by
    intro h; rw [h, hr1] at hr0; exact absurd (j.injective hr0) (by decide)
  -- the vertex certificate
  have hA := hgV.1
  have hli4 : LinearIndependent ℝ (fun r => row squareSides (y (i r))) := by
    have := Matrix.linearIndependent_rows_iff_isUnit.mpr
      ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hA))
    exact this
  have hli : LinearIndependent ℝ
      (fun r : (Finset.univ : Finset (Fin 4)) => row squareSides ((y ∘ i) r)) :=
    hli4.comp Subtype.val Subtype.val_injective
  have he : (Pi.single 0 1 : Fin 4 → ℝ) =
      ∑ r ∈ Finset.univ, vertexCert squareSides (y ∘ i) r • row squareSides ((y ∘ i) r) := by
    funext c
    have := vertexCert_eq squareSides (y ∘ i) hA c
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, smul_eq_mul, Pi.single_apply]
    exact this.symm
  rcases square_support (fun r _ => hgV.2.1 r) hli he with hV' | hS' | hN
  · exfalso
    have hc := hV' k
    have : 1 < (onSide (y ∘ i) Finset.univ k).card := Finset.one_lt_card.mpr
      ⟨r0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
        change (y (i r0)).1 = k; rw [hr0]; exact hg.1⟩,
       r1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
        change (y (i r1)).1 = k; rw [hr1]; exact hg.2.1⟩, hr01⟩
    omega
  · exfalso
    obtain ⟨_, a, b, c, htt, -⟩ := hS'
    have := Finset.card_le_three (a := a) (b := b) (c := c)
    rw [← htt, Finset.card_univ, Fintype.card_fin] at this
    omega
  · obtain ⟨a, -, b, -, hside, hpos⟩ := hN
    have hab : a ≠ b := by
      intro h; rw [h] at hside; exact fin4_add_two_ne _ hside.symm
    exact badP_of_opp y (i.injective.ne hab) ⟨hside, hpos⟩

/-- Segment candidates on a pair and on the reversed pair: only on a null event. -/
lemma seg_rev_null (T : ℝ) (k : Fin 4) (ω : PoissonPP.Sample (Pt 4))
    (hS : HasSegCand squareSides k (k + 2) T ω)
    (hS' : HasSegCand squareSides (k + 2) (k + 2 + 2) T ω) :
    BadExtra squareSides (segBase squareSides k (k + 2)) ω := by
  obtain ⟨n, y⟩ := ω
  by_contra hbad
  obtain ⟨i, hg, c, -, hf⟩ := hS
  obtain ⟨j, hg', c', -, hf'⟩ := hS'
  have hP := squarePair k
  have hP' := squarePair (k + 2)
  have hfi := (feasible_config_iff squareSides y _).mp hf
  have hfj := (feasible_config_iff squareSides y _).mp hf'
  have h1 := (seg_optimal hP hg _ fun r => hfj (i r)).1
  have h2 := seg_optimal hP' hg' _ fun r => hfi (j r)
  rw [segCopy_fst] at h1 h2
  have hrange : ∀ r, ∃ r', i r' = j r := by
    intro r
    have ht := h2.2 (le_antisymm h2.1 h1).symm r
    have hside : (y (j r)).1 = k ∨ (y (j r)).1 = k + 2 := by
      match r with
      | 0 => exact Or.inr hg'.1
      | 1 => exact Or.inr hg'.2.1
      | 2 => left; have := hg'.2.2.1; rw [fin4_add_two_add_two] at this; exact this
    change gx squareSides (segCopy squareSides k (segVec squareSides k (k + 2) (y ∘ i)) c)
      (y (j r)) = 0 at ht
    rw [gx_segCopy_side hP _ _ _ hside] at ht
    obtain ⟨r', hr'⟩ := seg_tight_in_range y hbad i (j r) ht
    exact ⟨r', hr'⟩
  -- both points of the reversed pair on side `k + 2` are the single point `i 2`
  have hk : ∀ r, (y (j r)).1 = k + 2 → ∀ r', i r' = j r → r' = 2 := by
    intro r hr r' he
    have a0 : (y (i 0)).1 = k := hg.1
    have a1 : (y (i 1)).1 = k := hg.2.1
    match r', he with
    | 0, he => rw [← he, a0] at hr; exact absurd hr.symm (fin4_add_two_ne k)
    | 1, he => rw [← he, a1] at hr; exact absurd hr.symm (fin4_add_two_ne k)
    | 2, _ => rfl
  obtain ⟨r0, hr0⟩ := hrange 0
  obtain ⟨r1, hr1⟩ := hrange 1
  have e0 := hk 0 hg'.1 r0 hr0
  have e1 := hk 1 hg'.2.1 r1 hr1
  rw [e0] at hr0; rw [e1] at hr1
  exact absurd (j.injective (hr0.symm.trans hr1)) (by decide)

/-- Segment candidates on perpendicular pairs: only on a null event. -/
lemma seg_perp_null (T : ℝ) (k : Fin 4) (ω : PoissonPP.Sample (Pt 4))
    (hS : HasSegCand squareSides k (k + 2) T ω)
    (hS' : HasSegCand squareSides (k + 1) (k + 1 + 2) T ω) :
    BadExtra squareSides (vertexCopy squareSides) ω := by
  obtain ⟨n, y⟩ := ω
  by_contra hbad
  obtain ⟨i, hg, c, -, hf⟩ := hS
  obtain ⟨j, hg', c', -, hf'⟩ := hS'
  have hP := squarePair k
  have hP' := squarePair (k + 1)
  have hfi := (feasible_config_iff squareSides y _).mp hf
  have hfj := (feasible_config_iff squareSides y _).mp hf'
  have h1 := (seg_optimal hP hg _ fun r => hfj (i r)).1
  have h2 := seg_optimal hP' hg' _ fun r => hfi (j r)
  rw [segCopy_fst] at h1 h2
  set zS := segCopy squareSides k (segVec squareSides k (k + 2) (y ∘ i)) c
  have htj : ∀ r, gx squareSides zS (y (j r)) = 0 := h2.2 (le_antisymm h2.1 h1).symm
  have hsi : ∀ r, (y (i r)).1 = k ∨ (y (i r)).1 = k + 2 := fun r => by
    match r with
    | 0 => exact Or.inl hg.1
    | 1 => exact Or.inl hg.2.1
    | 2 => exact Or.inr hg.2.2.1
  have hj0 : (y (j 0)).1 = k + 1 := hg'.1
  have hj1 : (y (j 1)).1 = k + 1 := hg'.2.1
  have hij : ∀ r, i r ≠ j 0 ∧ i r ≠ j 1 := by
    intro r
    constructor <;> intro he <;> rcases hsi r with h | h
    · rw [he, hj0] at h; exact fin4_succ_ne k h
    · rw [he, hj0] at h; exact fin4_succ_ne_two k h
    · rw [he, hj1] at h; exact fin4_succ_ne k h
    · rw [he, hj1] at h; exact fin4_succ_ne_two k h
  let f : Fin 4 ↪ Fin n := ⟨![i 0, i 1, i 2, j 0], fun r r' hr => by
    have h01 : i 0 ≠ i 1 := i.injective.ne (by decide)
    have h02 : i 0 ≠ i 2 := i.injective.ne (by decide)
    have h12 : i 1 ≠ i 2 := i.injective.ne (by decide)
    have := hij 0; have := hij 1; have := hij 2
    fin_cases r <;> fin_cases r' <;> simp_all [eq_comm]⟩
  have hdet : (vertexMatrix squareSides (y ∘ f)).det ≠ 0 :=
    perp_rows_det k (y ∘ f) hg.1 hg.2.1 hg.2.2.1 hj0 hg.lt.ne
  have hz : vertexCopy squareSides (y ∘ f) = zS := by
    apply vertexCopy_eq_of_tight squareSides _ hdet
    intro r
    fin_cases r
    · exact segCopy_tight hP hg c 0
    · exact segCopy_tight hP hg c 1
    · exact segCopy_tight hP hg c 2
    · exact htj 0
  have ht1 : gx squareSides (vertexCopy squareSides (y ∘ f)) (y (j 1)) = 0 := by
    rw [hz]; exact htj 1
  obtain ⟨r, hr⟩ := tight_index_in_range squareSides y hbad f (j 1) ht1
  fin_cases r
  · exact (hij 0).2 hr
  · exact (hij 1).2 hr
  · exact (hij 2).2 hr
  · exact absurd (j.injective hr) (by decide)

/-! ### `P(E) → 1/4` for the square -/

/-- The union of the five candidate events. -/
def candU (T : ℝ) : Set (PoissonPP.Sample (Pt 4)) :=
  {ω | HasVertexCandidate squareSides T ω} ∪ ⋃ k : Fin 4, {ω | HasSegCand squareSides k (k + 2) T ω}

/-- The null events used by the classification. -/
def nullN : Set (PoissonPP.Sample (Pt 4)) :=
  ({ω | BadExtra squareSides (vertexCopy squareSides) ω} ∪ {ω | BadP OppP ω}) ∪
    ⋃ k : Fin 4, {ω | BadExtra squareSides (segBase squareSides k (k + 2)) ω}

lemma nullN_zero (T : ℝ) : PoissonPP.law (Λ squareSides T) nullN = 0 :=
  measure_union_null (measure_union_null (no_extra_tight_vertex squareSides T) (opp_null T))
    (measure_iUnion_null fun k =>
      badExtra_prob_zero squareSides _ (measurable_segBase squareSides k (k + 2)) T)

lemma seg_pair_null (T : ℝ) {k k' : Fin 4} (hkk : k ≠ k') :
    {ω | HasSegCand squareSides k (k + 2) T ω} ∩ {ω | HasSegCand squareSides k' (k' + 2) T ω} ⊆
      nullN := by
  rintro ω ⟨h, h'⟩
  have hc : k' = k + 1 ∨ k' = k + 2 ∨ k' = k + 3 := by
    fin_cases k <;> fin_cases k' <;> simp_all <;> decide
  rcases hc with rfl | rfl | rfl
  · exact Or.inl (Or.inl (seg_perp_null T k ω h h'))
  · exact Or.inr (mem_iUnion.mpr ⟨k, seg_rev_null T k ω h h'⟩)
  · have h'' : HasSegCand squareSides (k + 3 + 1) (k + 3 + 1 + 2) T ω := by
      rw [fin4_three_succ]; exact h
    exact Or.inl (Or.inl (seg_perp_null T (k + 3) ω h' h''))

/-- **The probability of `E` in the truncated model**: the vertex-candidate probability plus
the four segment-candidate probabilities. -/
theorem square_optFit_prob (T : ℝ) :
    PoissonPP.law (Λ squareSides T) {ω | OptFit squareSides T ω} =
      PoissonPP.law (Λ squareSides T) {ω | HasVertexCandidate squareSides T ω} +
        ∑ k : Fin 4, PoissonPP.law (Λ squareSides T) {ω | HasSegCand squareSides k (k + 2) T ω} := by
  set μ := PoissonPP.law (Λ squareSides T)
  have hsub : candU T ⊆ {ω | OptFit squareSides T ω} := by
    rintro ω (h | h)
    · exact optFit_of_vertex squareSides T ω h
    · obtain ⟨k, hk⟩ := mem_iUnion.mp h
      exact optFit_of_seg squareSides (squarePair k) T ω hk
  have hsup : {ω | OptFit squareSides T ω} ⊆ candU T ∪ nullN := by
    intro ω h
    rcases square_classify T ω h with hV | ⟨k, hk⟩ | hN
    · exact Or.inl (Or.inl hV)
    · exact Or.inl (Or.inr (mem_iUnion.mpr ⟨k, hk⟩))
    · exact Or.inr (Or.inl (Or.inr hN))
  have hE : μ {ω | OptFit squareSides T ω} = μ (candU T) := by
    apply le_antisymm
    · calc μ {ω | OptFit squareSides T ω} ≤ μ (candU T ∪ nullN) := measure_mono hsup
        _ ≤ μ (candU T) + μ nullN := measure_union_le _ _
        _ = μ (candU T) := by rw [nullN_zero, add_zero]
    · exact measure_mono hsub
  have hSm : ∀ k : Fin 4, MeasurableSet {ω | HasSegCand squareSides k (k + 2) T ω} :=
    fun k => measurableSet_HasSegCand squareSides k (k + 2) T
  have hdisj : Pairwise (Function.onFun (AEDisjoint μ)
      fun k : Fin 4 => {ω | HasSegCand squareSides k (k + 2) T ω}) := by
    intro k k' hkk
    exact measure_mono_null (seg_pair_null T hkk) (nullN_zero T)
  have hVS : AEDisjoint μ {ω | HasVertexCandidate squareSides T ω}
      (⋃ k : Fin 4, {ω | HasSegCand squareSides k (k + 2) T ω}) := by
    apply measure_mono_null _ (nullN_zero T)
    rintro ω ⟨hV, hS⟩
    obtain ⟨k, hk⟩ := mem_iUnion.mp hS
    rcases vertex_seg_null T k ω hV hk with h | h
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr h)
  rw [hE, candU, measure_union₀ (MeasurableSet.iUnion hSm).nullMeasurableSet hVS,
    measure_iUnion₀ hdisj fun k => (hSm k).nullMeasurableSet, tsum_fintype]

/-- **`p₄ = 1/4` in the Poisson model.** In the model truncated at depth `n`, the probability that
some optimal copy fits (with its lines below the cutoff) tends to `1/4`. -/
theorem square_optFit_limit :
    Filter.Tendsto (fun n : ℕ => PoissonPP.law (Λ squareSides n) {ω | OptFit squareSides n ω})
      Filter.atTop (nhds (ENNReal.ofReal (1 / 4))) := by
  simp_rw [square_optFit_prob]
  exact square_candidates_limit

end Enclosing
