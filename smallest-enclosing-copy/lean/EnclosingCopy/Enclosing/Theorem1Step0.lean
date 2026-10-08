import EnclosingCopy.Enclosing.Theorem1Limit
import EnclosingCopy.Enclosing.PolygonArea
import Mathlib.Analysis.Convex.Measure

/-!
# Theorem 1, Step 0: the rotation localises

A copy of the polygon `P` is `simCopy l θ c = {l R_θ y + c : y ∈ P}`.

* `volume_simCopy`: rotations have determinant one, so a copy has area `l²`;
* `eq_of_subset_volume`: a closed set inside a closed convex body of no larger finite area,
  with nonempty interior, is all of it;
* `step0`: for every `η > 0` there is `β > 0` such that a copy of scale below `1 + β`
  containing `P` has its rotation within `η` of a symmetry angle (compactness in
  `(l, θ, c)`, then equal areas);
* `step0_sample`: the same for copies containing a sample that covers `P` to within `δ`;
* `simCopy_symm`: rotating by a symmetry angle gives the same family of sets.
-/

namespace Enclosing
open MeasureTheory Set Filter Topology Real Metric
open scoped Pointwise

variable {m : ℕ} (K : Sides m)

/-- The similarity `y ↦ l R_θ y + c`. -/
noncomputable def simMap (l θ : ℝ) (c : ℝ × ℝ) (y : ℝ × ℝ) : ℝ × ℝ := l • planeRotate θ y + c

/-- A copy of the polygon. -/
noncomputable def simCopy (l θ : ℝ) (c : ℝ × ℝ) : Set (ℝ × ℝ) :=
  simMap l θ c '' polygonRegion K

/-- `θ₀` is a rotational symmetry of the polygon up to translation. -/
def SymAngle (θ₀ : ℝ) : Prop :=
  ∃ t : ℝ × ℝ, planeRotate θ₀ '' polygonRegion K = (· + t) '' polygonRegion K

/-- Rotation as a linear map. -/
noncomputable def rotLin (θ : ℝ) : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ) where
  toFun := planeRotate θ
  map_add' x y := by apply Prod.ext <;> simp [planeRotate] <;> ring
  map_smul' r x := by apply Prod.ext <;> simp [planeRotate] <;> ring

lemma det_rotLin (θ : ℝ) : LinearMap.det (rotLin θ) = 1 := by
  rw [← LinearMap.det_toMatrix (Module.Basis.finTwoProd ℝ), Matrix.det_fin_two]
  simp [LinearMap.toMatrix_apply, rotLin, planeRotate]
  nlinarith [sin_sq_add_cos_sq θ]

lemma planeRotate_add (a b : ℝ) (x : ℝ × ℝ) :
    planeRotate (a + b) x = planeRotate a (planeRotate b x) := by
  apply Prod.ext <;> simp [planeRotate, cos_add, sin_add] <;> ring

lemma planeRotate_periodic (θ : ℝ) (k : ℤ) (x : ℝ × ℝ) :
    planeRotate (θ + k * (2 * π)) x = planeRotate θ x := by
  simp [planeRotate, cos_add_int_mul_two_pi, sin_add_int_mul_two_pi]

lemma continuous_planeRotate : Continuous fun p : ℝ × (ℝ × ℝ) => planeRotate p.1 p.2 := by
  unfold planeRotate; fun_prop

lemma volume_simCopy (l θ : ℝ) (c : ℝ × ℝ) :
    volume (simCopy K l θ c) = ENNReal.ofReal (l ^ 2) * volume (polygonRegion K) := by
  have he : simCopy K l θ c = (fun x => x + c) '' (l • (rotLin θ '' polygonRegion K)) := by
    unfold simCopy simMap
    rw [← image_smul, image_image, image_image]
    rfl
  rw [he, image_add_right, measure_preimage_add_right, Measure.addHaar_smul,
    Module.finrank_prod, Module.finrank_self, Measure.addHaar_image_linearMap, det_rotLin]
  simp

/-- Nested convex bodies of equal finite area coincide. -/
lemma eq_of_subset_volume {P Q : Set (ℝ × ℝ)} (hP : IsClosed P) (hQc : Convex ℝ Q)
    (hQ : IsClosed Q) (hQi : (interior Q).Nonempty) (hsub : P ⊆ Q)
    (hvol : volume Q ≤ volume P) (hfin : volume P ≠ ⊤) : P = Q := by
  by_contra hne
  obtain ⟨y, hyQ, hyP⟩ : ∃ y ∈ Q, y ∉ P := by
    by_contra h; push Not at h; exact hne (subset_antisymm hsub h)
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hP.isOpen_compl y hyP
  have hcl : y ∈ closure (interior Q) := by
    rw [hQc.closure_interior_eq_closure_of_nonempty_interior hQi, hQ.closure_eq]; exact hyQ
  obtain ⟨w, hwB, hwI⟩ := Metric.mem_closure_iff.mp hcl ε hε |> fun ⟨w, hw, hd⟩ =>
    (⟨w, show w ∈ ball y ε by rw [mem_ball, dist_comm]; exact hd, hw⟩ :
      ∃ w, w ∈ ball y ε ∧ w ∈ interior Q)
  let U := interior Q ∩ ball y ε
  have hU : IsOpen U := isOpen_interior.inter isOpen_ball
  have hUpos : 0 < volume U := hU.measure_pos _ ⟨w, hwI, hwB⟩
  have hUsub : U ⊆ Q \ P := fun z hz => ⟨interior_subset hz.1, fun hzP => hball hz.2 hzP⟩
  have hdisj : Disjoint P U := by
    rw [Set.disjoint_left]; intro z hzP hzU; exact (hUsub hzU).2 hzP
  have hle : volume P + volume U ≤ volume Q := by
    rw [← measure_union hdisj hU.measurableSet]
    exact measure_mono (union_subset hsub fun z hz => (hUsub hz).1)
  have := hle.trans hvol
  have h2 : volume P + volume U ≤ volume P + 0 := by simpa using this
  have := (ENNReal.add_le_add_iff_left hfin).1 h2
  exact absurd hUpos (not_lt.mpr this)

/-! ### The compactness argument -/

lemma convex_polygonRegion : Convex ℝ (polygonRegion K) := by
  intro x hx y hy a b ha hb hab i
  have h1 := hx i
  have h2 := hy i
  simp only [dot, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at h1 h2 ⊢
  calc (a * x.1 + b * y.1) * (K.u i).1 + (a * x.2 + b * y.2) * (K.u i).2
      = a * (x.1 * (K.u i).1 + x.2 * (K.u i).2) + b * (y.1 * (K.u i).1 + y.2 * (K.u i).2) := by
        ring
    _ ≤ a * K.h i + b * K.h i :=
        add_le_add (mul_le_mul_of_nonneg_left h1 ha) (mul_le_mul_of_nonneg_left h2 hb)
    _ = K.h i := by rw [← add_mul, hab, one_mul]

/-- A convex set of positive area has nonempty interior. -/
lemma interior_nonempty_of_volume_pos {S : Set (ℝ × ℝ)} (hS : Convex ℝ S) (hv : 0 < volume S) :
    (interior S).Nonempty := by
  by_contra h
  rw [Set.not_nonempty_iff_eq_empty] at h
  have hsub : S ⊆ frontier S := by
    intro x hx
    refine ⟨subset_closure hx, ?_⟩
    rw [h]; exact Set.notMem_empty x
  have := measure_mono_null hsub (Convex.addHaar_frontier volume hS)
  exact (ne_of_gt hv) this

lemma simCopy_eq_image (l θ : ℝ) (c : ℝ × ℝ) :
    simCopy K l θ c = (fun x => x + c) '' ((l • rotLin θ) '' polygonRegion K) := by
  unfold simCopy simMap; rw [image_image]; rfl

lemma convex_simCopy (l θ : ℝ) (c : ℝ × ℝ) : Convex ℝ (simCopy K l θ c) := by
  rintro _ ⟨y₁, hy₁, rfl⟩ _ ⟨y₂, hy₂, rfl⟩ a b ha hb hab
  refine ⟨a • y₁ + b • y₂, convex_polygonRegion K hy₁ hy₂ ha hb hab, ?_⟩
  have hb' : b = 1 - a := by linarith
  subst hb'
  apply Prod.ext <;> simp [simMap, planeRotate] <;> ring

lemma continuous_simMap_uncurry :
    Continuous fun p : (ℝ × ℝ × (ℝ × ℝ)) × (ℝ × ℝ) => simMap p.1.1 p.1.2.1 p.1.2.2 p.2 := by
  unfold simMap planeRotate; fun_prop

variable [NeZero m]

lemma isCompact_simCopy (hG : GoodSides K) (l θ : ℝ) (c : ℝ × ℝ) : IsCompact (simCopy K l θ c) :=
  (isCompact_polygonRegion K hG).image (by unfold simMap planeRotate; fun_prop)

lemma norm_planeRotate_le (θ : ℝ) (y : ℝ × ℝ) : ‖planeRotate θ y‖ ≤ 2 * ‖y‖ := by
  have h1 : |y.1| ≤ ‖y‖ := norm_fst_le y
  have h2 : |y.2| ≤ ‖y‖ := norm_snd_le y
  have hc := abs_cos_le_one θ
  have hs := abs_sin_le_one θ
  rw [Prod.norm_def, max_le_iff]
  simp only [planeRotate, Real.norm_eq_abs]
  constructor
  · calc |cos θ * y.1 - sin θ * y.2| ≤ |cos θ| * |y.1| + |sin θ| * |y.2| := by
          rw [← abs_mul, ← abs_mul]; exact abs_sub _ _
      _ ≤ 1 * ‖y‖ + 1 * ‖y‖ := by gcongr
      _ = 2 * ‖y‖ := by ring
  · calc |sin θ * y.1 + cos θ * y.2| ≤ |sin θ| * |y.1| + |cos θ| * |y.2| := by
          rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
      _ ≤ 1 * ‖y‖ + 1 * ‖y‖ := by gcongr
      _ = 2 * ‖y‖ := by ring

omit [NeZero m] in
lemma simCopy_periodic (l θ : ℝ) (k : ℤ) (c : ℝ × ℝ) :
    simCopy K l (θ + k * (2 * π)) c = simCopy K l θ c := by
  unfold simCopy simMap; simp only [planeRotate_periodic]

omit [NeZero m] in
lemma symAngle_periodic {θ₀ : ℝ} (h : SymAngle K θ₀) (k : ℤ) :
    SymAngle K (θ₀ + k * (2 * π)) := by
  obtain ⟨t, ht⟩ := h
  refine ⟨t, ?_⟩
  rw [← ht]; ext x; simp only [mem_image, planeRotate_periodic]

/-- **Step 0.** -/
theorem step0 (hG : GoodSides K) (hv : volume (polygonRegion K) = 1) {η : ℝ} (hη : 0 < η) :
    ∃ β > 0, ∀ l θ c, 0 < l → l < 1 + β → polygonRegion K ⊆ simCopy K l θ c →
      ∃ θ₀, SymAngle K θ₀ ∧ |θ - θ₀| < η := by
  set P := polygonRegion K
  have hPc : IsCompact P := isCompact_polygonRegion K hG
  have hPne : P.Nonempty := by
    by_contra h; rw [Set.not_nonempty_iff_eq_empty] at h; rw [h, measure_empty] at hv
    exact zero_ne_one hv
  obtain ⟨x₀, hx₀⟩ := hPne
  obtain ⟨ρ, hρ⟩ := hPc.isBounded.subset_closedBall 0
  have hfin : volume P ≠ ⊤ := by rw [hv]; exact ENNReal.one_ne_top
  have hl1 : ∀ l θ c, 0 < l → P ⊆ simCopy K l θ c → 1 ≤ l := by
    intro l θ c hl hsub
    have h := measure_mono (μ := volume) hsub
    rw [volume_simCopy, hv, mul_one] at h
    have : (1 : ℝ) ≤ l ^ 2 := by
      have := (ENNReal.one_le_ofReal).1 h; exact this
    nlinarith
  have hcb : ∀ l θ c, 0 < l → l ≤ 2 → P ⊆ simCopy K l θ c →
      c ∈ closedBall (0 : ℝ × ℝ) (5 * ρ) := by
    intro l θ c hl hl2 hsub
    have hl0 : 0 ≤ l := hl.le
    obtain ⟨y, hy, hxy⟩ := hsub hx₀
    have hy' := hρ hy
    have hx' := hρ hx₀
    rw [mem_closedBall, dist_zero_right] at hy' hx' ⊢
    have hc : c = x₀ - l • planeRotate θ y := by rw [← hxy]; simp [simMap]
    rw [hc]
    calc ‖x₀ - l • planeRotate θ y‖ ≤ ‖x₀‖ + ‖l • planeRotate θ y‖ := norm_sub_le _ _
      _ ≤ ρ + l * (2 * ρ) := by
          rw [norm_smul, Real.norm_of_nonneg hl0]
          gcongr
          exact (norm_planeRotate_le θ y).trans (by linarith)
      _ ≤ 5 * ρ := by
          have : 0 ≤ ρ := le_trans (norm_nonneg _) hx'
          nlinarith
  have hnorm : ∀ θ : ℝ, ∃ θ' ∈ Icc (-π) π, ∃ k : ℤ, θ = θ' + k * (2 * π) := by
    intro θ
    refine ⟨toIcoMod two_pi_pos (-π) θ, ?_, toIcoDiv two_pi_pos (-π) θ, ?_⟩
    · have := toIcoMod_mem_Ico two_pi_pos (-π) θ
      exact ⟨this.1, by linarith [this.2]⟩
    · have := toIcoMod_add_toIcoDiv_zsmul two_pi_pos (-π) θ
      rw [zsmul_eq_mul] at this; linarith
  let Z : Set (ℝ × ℝ × (ℝ × ℝ)) := {p | p.1 ∈ Icc 1 2 ∧ p.2.1 ∈ Icc (-π) π ∧
    p.2.2 ∈ closedBall (0 : ℝ × ℝ) (5 * ρ) ∧ P ⊆ simCopy K p.1 p.2.1 p.2.2 ∧
    ∀ θ₀, SymAngle K θ₀ → η ≤ |p.2.1 - θ₀|}
  have hZc : IsCompact Z := by
    have hbox : IsCompact (Icc (1 : ℝ) 2 ×ˢ (Icc (-π) π ×ˢ closedBall (0 : ℝ × ℝ) (5 * ρ))) :=
      isCompact_Icc.prod (isCompact_Icc.prod (isCompact_closedBall _ _))
    refine hbox.of_isClosed_subset ?_ (fun p hp => ⟨hp.1, hp.2.1, hp.2.2.1⟩)
    have h1 : IsClosed {p : ℝ × ℝ × (ℝ × ℝ) | p.1 ∈ Icc 1 2} :=
      isClosed_Icc.preimage continuous_fst
    have h2 : IsClosed {p : ℝ × ℝ × (ℝ × ℝ) | p.2.1 ∈ Icc (-π) π} :=
      isClosed_Icc.preimage continuous_snd.fst
    have h3 : IsClosed {p : ℝ × ℝ × (ℝ × ℝ) | p.2.2 ∈ closedBall (0 : ℝ × ℝ) (5 * ρ)} :=
      isClosed_closedBall.preimage continuous_snd.snd
    have h4 : IsClosed {p : ℝ × ℝ × (ℝ × ℝ) | P ⊆ simCopy K p.1 p.2.1 p.2.2} := by
      have e : {p : ℝ × ℝ × (ℝ × ℝ) | P ⊆ simCopy K p.1 p.2.1 p.2.2} =
          ⋂ x ∈ P, {p | ∃ y ∈ P, (p, y) ∈
            {q : (ℝ × ℝ × (ℝ × ℝ)) × (ℝ × ℝ) | simMap q.1.1 q.1.2.1 q.1.2.2 q.2 = x}} := by
        ext p
        simp only [mem_setOf_eq, mem_iInter, simCopy, Set.subset_def, mem_image]
        exact Iff.rfl
      rw [e]
      exact isClosed_biInter fun x _ => isClosed_exists_mem_compact hPc
        (isClosed_eq continuous_simMap_uncurry continuous_const)
    have h5 : IsClosed {p : ℝ × ℝ × (ℝ × ℝ) | ∀ θ₀, SymAngle K θ₀ → η ≤ |p.2.1 - θ₀|} := by
      have e : {p : ℝ × ℝ × (ℝ × ℝ) | ∀ θ₀, SymAngle K θ₀ → η ≤ |p.2.1 - θ₀|} =
          ⋂ θ₀ ∈ {θ₀ | SymAngle K θ₀}, {p : ℝ × ℝ × (ℝ × ℝ) | η ≤ |p.2.1 - θ₀|} := by
        ext p; simp
      rw [e]
      exact isClosed_biInter fun θ₀ _ => isClosed_le continuous_const (by fun_prop)
    exact h1.inter (h2.inter (h3.inter (h4.inter h5)))
  have hsymOf : ∀ θ c, P = simCopy K 1 θ c → SymAngle K θ := by
    intro θ c heq
    refine ⟨-c, ?_⟩
    ext x
    simp only [mem_image]
    constructor
    · rintro ⟨y, hy, rfl⟩
      have hw : planeRotate θ y + c ∈ P := by
        rw [heq]; exact ⟨y, hy, by simp [simMap]⟩
      exact ⟨_, hw, by abel⟩
    · rintro ⟨w, hw, rfl⟩
      have hw' : w ∈ simCopy K 1 θ c := by rw [← heq]; exact hw
      obtain ⟨y, hy, hyw⟩ := hw'
      refine ⟨y, hy, ?_⟩
      rw [← hyw]; simp [simMap]
  by_cases hZ : Z.Nonempty
  · obtain ⟨p, hpZ, hpmin⟩ := hZc.exists_isMinOn hZ continuous_fst.continuousOn
    have hp1 : 1 < p.1 := by
      rcases eq_or_lt_of_le hpZ.1.1 with h | h
      · exfalso
        have hsub := hpZ.2.2.2.1
        rw [← h] at hsub
        have hvol' : volume (simCopy K 1 p.2.1 p.2.2) ≤ volume P := by
          rw [volume_simCopy]; simp; exact le_rfl
        have hint := interior_nonempty_of_volume_pos (convex_simCopy K 1 p.2.1 p.2.2)
          (by rw [volume_simCopy, hv]; simp)
        have heq := eq_of_subset_volume (isClosed_polygonRegion K) (convex_simCopy K 1 _ _)
          (isCompact_simCopy K hG 1 _ _).isClosed hint hsub hvol' hfin
        have := hpZ.2.2.2.2 p.2.1 (hsymOf _ _ heq)
        simp at this; linarith
      · exact h
    refine ⟨min (p.1 - 1) 1, lt_min (by linarith) one_pos, fun l θ c hl hlβ hsub => ?_⟩
    by_contra hno
    push Not at hno
    obtain ⟨θ', hθ', k, rfl⟩ := hnorm θ
    rw [simCopy_periodic] at hsub
    have hl2 : l ≤ 2 := by linarith [min_le_right (p.1 - 1) 1]
    have hmem : (l, θ', c) ∈ Z := by
      refine ⟨⟨hl1 l θ' c hl hsub, hl2⟩, hθ', hcb l θ' c hl hl2 hsub, hsub, fun θ₀ hθ₀ => ?_⟩
      have := hno (θ₀ + k * (2 * π)) (symAngle_periodic K hθ₀ k)
      calc η ≤ |θ' + k * (2 * π) - (θ₀ + k * (2 * π))| := this
        _ = |θ' - θ₀| := by ring_nf
    have := hpmin hmem
    simp only [mem_setOf_eq] at this
    linarith [min_le_left (p.1 - 1) 1]
  · refine ⟨1, one_pos, fun l θ c hl hlβ hsub => ?_⟩
    by_contra hno
    push Not at hno
    obtain ⟨θ', hθ', k, rfl⟩ := hnorm θ
    rw [simCopy_periodic] at hsub
    refine hZ ⟨(l, θ', c), ⟨hl1 l θ' c hl hsub, by linarith⟩, hθ',
      hcb l θ' c hl (by linarith) hsub, hsub, fun θ₀ hθ₀ => ?_⟩
    have := hno (θ₀ + k * (2 * π)) (symAngle_periodic K hθ₀ k)
    calc η ≤ |θ' + k * (2 * π) - (θ₀ + k * (2 * π))| := this
      _ = |θ' - θ₀| := by ring_nf

omit [NeZero m] in
lemma planeRotate_zero (x : ℝ × ℝ) : planeRotate 0 x = x := by
  apply Prod.ext <;> simp [planeRotate]

omit [NeZero m] in
lemma planeRotate_neg_cancel (θ : ℝ) (x : ℝ × ℝ) : planeRotate θ (planeRotate (-θ) x) = x := by
  rw [← planeRotate_add, add_neg_cancel, planeRotate_zero]

omit [NeZero m] in
/-- **Rotating by a symmetry angle gives the same family of copies.** -/
lemma simCopy_symm {θ₀ : ℝ} (h : SymAngle K θ₀) (l θ : ℝ) (c : ℝ × ℝ) :
    ∃ c', simCopy K l θ c = simCopy K l (θ - θ₀) c' := by
  obtain ⟨t, ht⟩ := h
  refine ⟨c + l • planeRotate (θ - θ₀) t, ?_⟩
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    have hw : planeRotate θ₀ y ∈ (· + t) '' polygonRegion K := by rw [← ht]; exact ⟨y, hy, rfl⟩
    obtain ⟨w, hw, hwt⟩ := hw
    refine ⟨w, hw, ?_⟩
    have : planeRotate θ y = planeRotate (θ - θ₀) (planeRotate θ₀ y) := by
      rw [← planeRotate_add]; ring_nf
    simp only [simMap, this, ← hwt]
    apply Prod.ext <;> simp [planeRotate] <;> ring
  · rintro ⟨w, hw, rfl⟩
    have hw' : w + t ∈ planeRotate θ₀ '' polygonRegion K := by rw [ht]; exact ⟨w, hw, rfl⟩
    obtain ⟨y, hy, hyw⟩ := hw'
    refine ⟨y, hy, ?_⟩
    have : planeRotate θ y = planeRotate (θ - θ₀) (planeRotate θ₀ y) := by
      rw [← planeRotate_add]; ring_nf
    simp only [simMap, this, hyw]
    apply Prod.ext <;> simp [planeRotate] <;> ring

/-- **Step 0 for samples**: if a set `S` covers the polygon to within `δ`, every copy of scale at
most one containing `S` has its rotation within `η` of a symmetry angle. -/
theorem step0_sample (hG : GoodSides K) (hv : volume (polygonRegion K) = 1) {η : ℝ} (hη : 0 < η) :
    ∃ δ > 0, ∀ S : Set (ℝ × ℝ), (polygonRegion K ⊆ ⋃ s ∈ S, closedBall s δ) →
      ∀ l θ c, 0 < l → l ≤ 1 → S ⊆ simCopy K l θ c → ∃ θ₀, SymAngle K θ₀ ∧ |θ - θ₀| < η := by
  obtain ⟨β, hβ, hstep⟩ := step0 K hG hv hη
  set P := polygonRegion K
  have hint := interior_nonempty_of_volume_pos (convex_polygonRegion K) (by rw [hv]; exact one_pos)
  obtain ⟨p₀, hp₀⟩ := hint
  obtain ⟨r₀, hr₀, hball⟩ := Metric.isOpen_iff.mp isOpen_interior p₀ hp₀
  set r := r₀ / 2
  have hr : 0 < r := by positivity
  have hcb : closedBall p₀ r ⊆ P := fun x hx =>
    interior_subset (hball (closedBall_subset_ball (by simp only [r]; linarith) hx))
  refine ⟨β * r / 4, by positivity, fun S hS l θ c hl hl1 hsub => ?_⟩
  set δ := β * r / 4
  set σ := 2 * δ / r
  have hσ : 0 < σ := by positivity
  have hσβ : σ = β / 2 := by simp only [σ, δ]; field_simp; ring
  apply hstep (l + σ) θ (c - σ • planeRotate θ p₀) (by positivity) (by linarith)
  intro x hx
  obtain ⟨s, hs, hxs⟩ := mem_iUnion₂.mp (hS hx)
  obtain ⟨y, hy, rfl⟩ := hsub hs
  set e := x - simMap l θ c y
  have he : ‖e‖ ≤ δ := by rw [mem_closedBall, dist_eq_norm] at hxs; exact hxs
  set w := p₀ + (1 / σ) • planeRotate (-θ) e
  have hw : w ∈ P := by
    apply hcb
    rw [mem_closedBall, dist_eq_norm]
    simp only [w, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg (by positivity : 0 ≤ 1 / σ)]
    calc 1 / σ * ‖planeRotate (-θ) e‖ ≤ 1 / σ * (2 * δ) := by
          gcongr; exact (norm_planeRotate_le _ _).trans (by linarith)
      _ = r := by
          have hδ0 : δ ≠ 0 := by positivity
          simp only [σ]; field_simp
  have hlσ : 0 < l + σ := by positivity
  refine ⟨(l / (l + σ)) • y + (σ / (l + σ)) • w,
    convex_polygonRegion K hy hw (by positivity) (by positivity) (by field_simp), ?_⟩
  have hrot := planeRotate_neg_cancel θ e
  have hex : x = simMap l θ c y + e := by simp [e]
  rw [hex]
  have hlin : ∀ (a b : ℝ) (u v : ℝ × ℝ), planeRotate θ (a • u + b • v) =
      a • planeRotate θ u + b • planeRotate θ v := by
    intro a b u v; apply Prod.ext <;> simp [planeRotate] <;> ring
  have hR : planeRotate θ (p₀ + (1 / σ) • planeRotate (-θ) e) =
      planeRotate θ p₀ + (1 / σ) • e := by
    rw [show p₀ + (1 / σ) • planeRotate (-θ) e = (1 : ℝ) • p₀ + (1 / σ) • planeRotate (-θ) e by
      simp, hlin, hrot, one_smul]
  simp only [simMap, w]
  rw [hlin, hR]
  apply Prod.ext <;> simp <;> field_simp <;> ring

end Enclosing
