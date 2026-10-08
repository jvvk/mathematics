import EnclosingCopy.Enclosing.ConvexPolygon
import EnclosingCopy.Poisson.Infinite
import Mathlib.MeasureTheory.Integral.Indicator

/-!
# The untruncated limit model

The paper's limit model has independent Poisson processes of intensity one on the infinite strips
`[aᵢ, bᵢ] × [0, ∞)`. We build it from independent depth slabs `(k, k+1]` (`model`, an infinite
product measure). The first `n` slabs (`trunc n ω`) form the truncated model `Λ K n` on every
relabelling-invariant event (`model_trunc`).

* `ae_good`: almost surely every point lies on its side and in its slab, and every side has
  points within `δ = Q/(2 per)` of both ends (their void probabilities `e^{-cn}` vanish);
* `tilt_bound`, `deep_ok`: with such witnesses, a copy with `ε ≤ 0` has bounded tilt, so points
  deeper than a threshold `T*` never bind (Lemma 5 of the paper, via `∑ Lᵢ Hᵢ = 2ε`);
* `stable`: hence for all large `n` the truncated event on the first `n` slabs is the event `E`;
* `untruncated_prob`: `P(E)` equals the Theorem 8 value; `untruncated_triangle`,
  `untruncated_equilateral`: Corollary 2 and `13/48`.
-/

namespace Enclosing
open MeasureTheory Set ENNReal Filter

variable {m : ℕ} (K : Sides m)

/-- The intensity of the depth slab `(k, k+1]`. -/
noncomputable def ΛS (k : ℕ) : Measure (Pt m) :=
  ∑ i, (Measure.dirac i).prod (volume.restrict (Icc (K.a i) (K.b i) ×ˢ Ioc (k : ℝ) (k + 1)))

/-- The intensity on depths `(0, T]`. -/
noncomputable def Λo (T : ℝ) : Measure (Pt m) :=
  ∑ i, (Measure.dirac i).prod (volume.restrict (Icc (K.a i) (K.b i) ×ˢ Ioc (0 : ℝ) T))

instance (k : ℕ) : IsFiniteMeasure (ΛS K k) := by
  unfold ΛS
  constructor
  rw [Measure.coe_finset_sum, Finset.sum_apply]
  refine ENNReal.sum_lt_top.2 fun i _ => ?_
  rw [Measure.dirac_prod, Measure.map_apply measurable_prodMk_left MeasurableSet.univ,
    preimage_univ, Measure.restrict_apply_univ]
  exact lt_of_le_of_lt (measure_mono (prod_mono subset_rfl Ioc_subset_Icc_self))
    (isCompact_Icc.prod isCompact_Icc).measure_lt_top

lemma sum_ΛS (n : ℕ) : ∑ k : Fin n, ΛS K k = Λo K n := by
  induction n with
  | zero =>
    simp only [Finset.univ_eq_empty, Finset.sum_empty, Λo, Nat.cast_zero, Ioc_self, prod_empty,
      Measure.restrict_empty, Measure.prod_zero, Finset.sum_const_zero]
  | succ n ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.coe_castSucc, Fin.val_last]
    rw [ih, Λo, Λo, ΛS, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Measure.prod_add, ← Measure.restrict_union
      (Set.disjoint_prod.2 (Or.inr (Ioc_disjoint_Ioc_of_le le_rfl)))
      (measurableSet_Icc.prod measurableSet_Ioc), ← prod_union,
      Ioc_union_Ioc_eq_Ioc (by positivity) (by linarith)]
    push_cast; rfl

lemma Λo_eq (T : ℝ) : Λo K T = Λ K T := by
  unfold Λo Λ
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  refine Measure.restrict_congr_set ?_
  rw [ae_eq_set]
  constructor
  · rw [diff_eq_empty.2 (prod_mono subset_rfl Ioc_subset_Icc_self)]; exact measure_empty
  · refine measure_mono_null (t := Icc (K.a i) (K.b i) ×ˢ {(0 : ℝ)}) ?_ ?_
    · rintro ⟨s, d⟩ ⟨⟨hs, hd⟩, hn⟩
      refine ⟨hs, ?_⟩
      by_contra h0
      exact hn ⟨hs, lt_of_le_of_ne hd.1 (Ne.symm h0), hd.2⟩
    · rw [Measure.volume_eq_prod, Measure.prod_prod, Real.volume_singleton, mul_zero]

/-- **The untruncated model**: independent Poisson samples on the depth slabs. -/
noncomputable def model : Measure (ℕ → PoissonPP.Sample (Pt m)) := PoissonPP.slabLaw (ΛS K)

instance : IsProbabilityMeasure (model K) := by unfold model; infer_instance

/-- The first `n` slabs, as one labelled sample. -/
def trunc (n : ℕ) (ω : ℕ → PoissonPP.Sample (Pt m)) : PoissonPP.Sample (Pt m) :=
  PoissonPP.concatFin n (PoissonPP.firstSlabs n ω)

lemma measurable_trunc (n : ℕ) : Measurable (trunc (m := m) n) :=
  (PoissonPP.measurable_concatFin n).comp (PoissonPP.measurable_firstSlabs n)

/-- Events that ignore the labels of the sampled points. -/
def LabelFree (A : Set (PoissonPP.Sample (Pt m))) : Prop :=
  ∀ n (x : Fin n → Pt m) (σ : Equiv.Perm (Fin n)), (⟨n, x ∘ σ⟩ : PoissonPP.Sample (Pt m)) ∈ A ↔
    (⟨n, x⟩ : PoissonPP.Sample (Pt m)) ∈ A

/-- **The first `n` slabs are the truncated model** on label-free measurable events. -/
theorem model_trunc (n : ℕ) {A : Set (PoissonPP.Sample (Pt m))} (hA : MeasurableSet A)
    (hfree : LabelFree A) :
    model K {ω | trunc n ω ∈ A} = PoissonPP.law (Λ K n) A := by
  have hinv : PoissonPP.PermInv (A.indicator (1 : PoissonPP.Sample (Pt m) → ℝ≥0∞)) := by
    intro j x σ
    by_cases h : (⟨j, x⟩ : PoissonPP.Sample (Pt m)) ∈ A
    · rw [indicator_of_mem h, indicator_of_mem ((hfree j x σ).2 h)]; rfl
    · rw [indicator_of_notMem h, indicator_of_notMem (fun h' => h ((hfree j x σ).1 h'))]
  have h := PoissonPP.lintegral_firstSlabs (ΛS K) n hinv (measurable_one.indicator hA)
  rw [sum_ΛS, Λo_eq, lintegral_indicator_one hA] at h
  rw [← h]
  change model K (trunc n ⁻¹' A) = _
  rw [← lintegral_indicator_one (hA.preimage (measurable_trunc n))]
  rfl

/-! ### The events of the classification are label-free -/

lemma emb_perm_iff {d n : ℕ} (Q : (Fin d → Pt m) → Multiset (Pt m) → Prop) (x : Fin n → Pt m)
    (σ : Equiv.Perm (Fin n)) :
    (∃ i : Fin d ↪ Fin n, Q ((x ∘ σ) ∘ i) (PoissonPP.config (x ∘ σ))) ↔
      ∃ i : Fin d ↪ Fin n, Q (x ∘ i) (PoissonPP.config x) := by
  rw [PoissonPP.config_comp_perm]
  constructor
  · rintro ⟨i, hi⟩; exact ⟨i.trans σ.toEmbedding, hi⟩
  · rintro ⟨i, hi⟩
    refine ⟨i.trans σ.symm.toEmbedding, ?_⟩
    have : (x ∘ σ) ∘ (i.trans σ.symm.toEmbedding) = x ∘ i := by
      funext r; simp
    rw [this]; exact hi

lemma labelFree_vertex (T : ℝ) : LabelFree {ω | HasVertexCandidate K T ω} := fun _ x σ =>
  emb_perm_iff (fun y c => VertexGood K T y ∧ Feasible K c (vertexCopy K y)) x σ

lemma labelFree_seg (k kb : Fin m) (T : ℝ) : LabelFree {ω | HasSegCand K k kb T ω} := fun _ x σ =>
  emb_perm_iff (fun y c => SegEvent K k kb T y c) x σ

lemma labelFree_badExtra {d : ℕ} (c : (Fin d → Pt m) → Copy) :
    LabelFree {ω | BadExtra K c ω} := fun _ x σ =>
  emb_perm_iff (fun y _ => extraTight K c y) x σ

lemma labelFree_badP {d : ℕ} (P : (Fin d → Pt m) → Pt m → Prop) :
    LabelFree {ω : PoissonPP.Sample (Pt m) | BadP P ω} := fun _ x σ =>
  emb_perm_iff (fun y _ => extraP P y) x σ

/-! ### The untruncated event and its stability -/

/-- All points of the untruncated configuration. -/
def allPts (ω : ℕ → PoissonPP.Sample (Pt m)) : Set (Pt m) :=
  {p | ∃ k, p ∈ PoissonPP.config (ω k).2}

/-- **The event `E` of the paper**, in the untruncated model: some copy that is optimal for all
the points fits. -/
def UFit (ω : ℕ → PoissonPP.Sample (Pt m)) : Prop :=
  ∃ z : Copy, Fits K z ∧ (∀ p ∈ allPts ω, ¬ violates K z p) ∧
    ∀ z' : Copy, (∀ p ∈ allPts ω, ¬ violates K z' p) → z.1 ≤ z'.1

omit K in
lemma mem_config_trunc (n : ℕ) (ω : ℕ → PoissonPP.Sample (Pt m)) (p : Pt m) :
    p ∈ PoissonPP.config (trunc n ω).2 ↔ ∃ k < n, p ∈ PoissonPP.config (ω k).2 := by
  rw [trunc, PoissonPP.mem_config_concatFin]
  constructor
  · rintro ⟨k, hk⟩; exact ⟨k, k.2, hk⟩
  · rintro ⟨k, hk, h⟩; exact ⟨⟨k, hk⟩, h⟩

/-- Side lengths, perimeter, `Q = ½ ∑ Lᵢ²` and the witness margin `δ = Q/(2 per)`. -/
noncomputable def Ls (i : Fin m) : ℝ := K.b i - K.a i
noncomputable def per : ℝ := ∑ i, Ls K i
noncomputable def Qs : ℝ := (∑ i, Ls K i ^ 2) / 2
noncomputable def δK : ℝ := Qs K / (2 * per K)

lemma Ls_pos (i : Fin m) : 0 < Ls K i := sub_pos.mpr (K.hab i)

lemma sum_Ls_Hs (z : Copy) : ∑ i, Ls K i * Hs K z i = 2 * z.1 := by
  have e : ∀ i, Ls K i * Hs K z i = z.1 * ((K.b i - K.a i) * K.h i) +
      z.2.1.1 * ((K.b i - K.a i) * (K.u i).1) + z.2.1.2 * ((K.b i - K.a i) * (K.u i).2) := by
    intro i; simp only [Ls, Hs, dot]; ring
  simp_rw [e, Finset.sum_add_distrib, ← Finset.mul_sum, K.sum_h, K.sum_u1, K.sum_u2]
  ring

lemma sum_Ls_b : ∑ i, Ls K i * K.b i = Qs K := by
  have h := K.sum_sq
  have e : ∀ i, K.b i ^ 2 - K.a i ^ 2 = 2 * (Ls K i * K.b i) - Ls K i ^ 2 := by
    intro i; simp only [Ls]; ring
  simp_rw [e, Finset.sum_sub_distrib, ← Finset.mul_sum] at h
  unfold Qs; linarith

lemma sum_Ls_a : ∑ i, Ls K i * K.a i = -Qs K := by
  have e : ∀ i, Ls K i * K.a i = Ls K i * K.b i - Ls K i ^ 2 := by intro i; simp only [Ls]; ring
  simp_rw [e, Finset.sum_sub_distrib, sum_Ls_b]
  unfold Qs; ring

/-- A feasible copy is above every point: `Hᵢ ≥ Θ s - D`. -/
lemma Hs_ge_of_not_violates {z : Copy} {p : Pt m} (h : ¬ violates K z p) :
    z.2.2 * p.2.1 - p.2.2 ≤ Hs K z p.1 := by
  unfold violates at h; linarith [not_lt.mp h]

lemma abs_le_of_mem_Icc {x a b : ℝ} (h : x ∈ Icc a b) : |x| ≤ |a| + |b| := by
  rw [abs_le]; constructor
  · linarith [neg_abs_le a, abs_nonneg b, h.1]
  · linarith [le_abs_self b, abs_nonneg a, h.2]

variable [NeZero m]

lemma per_pos : 0 < per K :=
  Finset.sum_pos (fun i _ => Ls_pos K i) ⟨0, Finset.mem_univ _⟩

lemma Qs_pos : 0 < Qs K := by
  unfold Qs
  have : 0 < ∑ i, Ls K i ^ 2 :=
    Finset.sum_pos (fun i _ => by have := Ls_pos K i; positivity) ⟨0, Finset.mem_univ _⟩
  positivity

lemma δK_pos : 0 < δK K := div_pos (Qs_pos K) (by have := per_pos K; positivity)

lemma δK_per : δK K * per K = Qs K / 2 := by
  have := (per_pos K).ne'
  unfold δK; field_simp

/-- **Coercivity**: a copy with `ε ≤ 0` above points near both ends of every side has a bounded
tilt. -/
lemma tilt_bound (wp wm : Fin m → Pt m) (hps : ∀ i, (wp i).1 = i) (hms : ∀ i, (wm i).1 = i)
    (hpp : ∀ i, K.b i - δK K ≤ (wp i).2.1) (hmm : ∀ i, (wm i).2.1 ≤ K.a i + δK K)
    (hpD : ∀ i, 0 ≤ (wp i).2.2) (hmD : ∀ i, 0 ≤ (wm i).2.2)
    (z : Copy) (hz : z.1 ≤ 0) (hp : ∀ i, ¬ violates K z (wp i)) (hm : ∀ i, ¬ violates K z (wm i)) :
    |z.2.2| ≤ 2 * (∑ i, Ls K i * ((wp i).2.2 + (wm i).2.2)) / Qs K := by
  set Θ := z.2.2
  have hQ := Qs_pos K
  have hsum := sum_Ls_Hs K z
  have hDp : 0 ≤ ∑ i, Ls K i * (wp i).2.2 :=
    Finset.sum_nonneg fun i _ => mul_nonneg (Ls_pos K i).le (hpD i)
  have hDm : 0 ≤ ∑ i, Ls K i * (wm i).2.2 :=
    Finset.sum_nonneg fun i _ => mul_nonneg (Ls_pos K i).le (hmD i)
  have hsplit : ∑ i, Ls K i * ((wp i).2.2 + (wm i).2.2) =
      ∑ i, Ls K i * (wp i).2.2 + ∑ i, Ls K i * (wm i).2.2 := by
    rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun i _ => by ring
  rw [hsplit, le_div_iff₀ hQ]
  rcases le_total 0 Θ with hΘ | hΘ
  · have h1 : ∀ i, Ls K i * (Θ * (K.b i - δK K) - (wp i).2.2) ≤ Ls K i * Hs K z i := by
      intro i
      have := Hs_ge_of_not_violates K (hp i)
      rw [hps i] at this
      exact mul_le_mul_of_nonneg_left (by nlinarith [hpp i]) (Ls_pos K i).le
    have h2 := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => h1 i
    have e : ∀ i, Ls K i * (Θ * (K.b i - δK K) - (wp i).2.2) =
        Θ * (Ls K i * K.b i) - Θ * δK K * Ls K i - Ls K i * (wp i).2.2 := fun i => by ring
    simp_rw [e, Finset.sum_sub_distrib, ← Finset.mul_sum, sum_Ls_b] at h2
    rw [hsum] at h2
    have hper := δK_per K
    unfold per at hper
    rw [abs_of_nonneg hΘ]
    nlinarith
  · have h1 : ∀ i, Ls K i * (Θ * (K.a i + δK K) - (wm i).2.2) ≤ Ls K i * Hs K z i := by
      intro i
      have := Hs_ge_of_not_violates K (hm i)
      rw [hms i] at this
      exact mul_le_mul_of_nonneg_left (by nlinarith [hmm i]) (Ls_pos K i).le
    have h2 := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => h1 i
    have e : ∀ i, Ls K i * (Θ * (K.a i + δK K) - (wm i).2.2) =
        Θ * (Ls K i * K.a i) + Θ * δK K * Ls K i - Ls K i * (wm i).2.2 := fun i => by ring
    simp_rw [e, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, sum_Ls_a] at h2
    rw [hsum] at h2
    have hper := δK_per K
    unfold per at hper
    rw [abs_of_nonpos hΘ]
    nlinarith

/-- Bound on the positions: `|s| ≤ ∑ (|aᵢ| + |bᵢ|)` on every side. -/
noncomputable def Sb : ℝ := ∑ i, (|K.a i| + |K.b i|)

omit [NeZero m] in
lemma single_le_Sb (i : Fin m) : |K.a i| + |K.b i| ≤ Sb K :=
  Finset.single_le_sum (f := fun i => |K.a i| + |K.b i|) (fun i _ => by positivity)
    (Finset.mem_univ i)

/-- The data of the witnesses: points near the right and left end of every side. -/
structure Wit (wp wm : Fin m → Pt m) : Prop where
  ps : ∀ i, (wp i).1 = i
  ms : ∀ i, (wm i).1 = i
  pp : ∀ i, K.b i - δK K ≤ (wp i).2.1
  mm : ∀ i, (wm i).2.1 ≤ K.a i + δK K
  pI : ∀ i, (wp i).2.1 ∈ Icc (K.a i) (K.b i)
  pD : ∀ i, 0 ≤ (wp i).2.2
  mD : ∀ i, 0 ≤ (wm i).2.2

variable {K}

/-- The tilt bound and depth threshold of a witness family. -/
noncomputable def tiltB (wp wm : Fin m → Pt m) : ℝ :=
  2 * (∑ i, Ls K i * ((wp i).2.2 + (wm i).2.2)) / Qs K
noncomputable def Dsum (wp wm : Fin m → Pt m) : ℝ := ∑ i, ((wp i).2.2 + (wm i).2.2)
noncomputable def Tstar (wp wm : Fin m → Pt m) : ℝ :=
  2 * tiltB (K := K) wp wm * Sb K + Dsum wp wm

/-- Below the witnesses, `Hᵢ ≥ -(B Sb + Dsum)`. -/
lemma Hs_lower {wp wm : Fin m → Pt m} (w : Wit K wp wm) {z : Copy} (hz : z.1 ≤ 0)
    (hp : ∀ i, ¬ violates K z (wp i)) (hm : ∀ i, ¬ violates K z (wm i)) (i : Fin m) :
    -(tiltB (K := K) wp wm * Sb K + Dsum wp wm) ≤ Hs K z i ∧ |z.2.2| ≤ tiltB (K := K) wp wm := by
  have hΘ := tilt_bound K wp wm w.ps w.ms w.pp w.mm w.pD w.mD z hz hp hm
  refine ⟨?_, hΘ⟩
  have h1 := Hs_ge_of_not_violates K (hp i)
  rw [w.ps i] at h1
  have hB : 0 ≤ tiltB (K := K) wp wm := le_trans (abs_nonneg _) hΘ
  have hs : |z.2.2 * (wp i).2.1| ≤ tiltB (K := K) wp wm * Sb K := by
    rw [abs_mul]
    exact mul_le_mul hΘ ((abs_le_of_mem_Icc (w.pI i)).trans (single_le_Sb K i)) (abs_nonneg _) hB
  have hD : (wp i).2.2 ≤ Dsum wp wm :=
    le_trans (le_add_of_nonneg_right (w.mD i))
      (Finset.single_le_sum (f := fun i => (wp i).2.2 + (wm i).2.2)
        (fun j _ => add_nonneg (w.pD j) (w.mD j)) (Finset.mem_univ i))
  linarith [neg_abs_le (z.2.2 * (wp i).2.1)]

/-- **Deep points never bind**: below the threshold `T*`, no admissible copy is violated. -/
lemma deep_ok {wp wm : Fin m → Pt m} (w : Wit K wp wm) {z : Copy} (hz : z.1 ≤ 0)
    (hp : ∀ i, ¬ violates K z (wp i)) (hm : ∀ i, ¬ violates K z (wm i)) (p : Pt m)
    (hpS : p.2.1 ∈ Icc (K.a p.1) (K.b p.1)) (hD : Tstar (K := K) wp wm ≤ p.2.2) :
    ¬ violates K z p := by
  obtain ⟨hH, hΘ⟩ := Hs_lower w hz hp hm p.1
  have hB : 0 ≤ tiltB (K := K) wp wm := le_trans (abs_nonneg _) hΘ
  have hs : z.2.2 * p.2.1 ≤ tiltB (K := K) wp wm * Sb K := by
    refine (le_abs_self _).trans ?_
    rw [abs_mul]
    exact mul_le_mul hΘ ((abs_le_of_mem_Icc hpS).trans (single_le_Sb K p.1)) (abs_nonneg _) hB
  unfold violates Tstar at *
  intro h
  linarith

lemma below_ok {wp wm : Fin m → Pt m} (w : Wit K wp wm) {z : Copy} (hz : z.1 ≤ 0)
    (hp : ∀ i, ¬ violates K z (wp i)) (hm : ∀ i, ¬ violates K z (wm i)) {T : ℝ}
    (hT : Tstar (K := K) wp wm ≤ T) : Below K T z := by
  intro i
  obtain ⟨hH, hΘ⟩ := Hs_lower w hz hp hm i
  have hB : 0 ≤ tiltB (K := K) wp wm := le_trans (abs_nonneg _) hΘ
  have hab := single_le_Sb K i
  have ha : z.2.2 * K.a i ≤ tiltB (K := K) wp wm * Sb K := by
    refine (le_abs_self _).trans ?_
    rw [abs_mul]
    exact mul_le_mul hΘ (le_trans (le_add_of_nonneg_right (abs_nonneg _)) hab) (abs_nonneg _) hB
  have hb : z.2.2 * K.b i ≤ tiltB (K := K) wp wm * Sb K := by
    refine (le_abs_self _).trans ?_
    rw [abs_mul]
    exact mul_le_mul hΘ (le_trans (le_add_of_nonneg_left (abs_nonneg _)) hab) (abs_nonneg _) hB
  unfold Tstar at hT
  have := max_le ha hb
  linarith

/-- The zero copy. -/
def zeroCopy : Copy := (0, (0, 0), 0)

omit [NeZero m] in
lemma not_violates_zero {p : Pt m} (h : 0 ≤ p.2.2) : ¬ violates K zeroCopy p := by
  simp only [violates, Hs, zeroCopy, dot]; intro h'; linarith

variable (K)

/-- The good event: points lie in their slabs and on their sides, and there are witnesses. -/
def Good (ω : ℕ → PoissonPP.Sample (Pt m)) : Prop :=
  (∀ k, ∀ p ∈ PoissonPP.config (ω k).2, p.2.1 ∈ Icc (K.a p.1) (K.b p.1) ∧
      p.2.2 ∈ Ioc (k : ℝ) (k + 1)) ∧
    ∀ i, (∃ p ∈ allPts ω, p.1 = i ∧ K.b i - δK K ≤ p.2.1) ∧
      (∃ p ∈ allPts ω, p.1 = i ∧ p.2.1 ≤ K.a i + δK K)

variable {K}

/-- **Stability**: on the good event, for all large `n` the truncated event `OptFit` at depth `n`
on the first `n` slabs is the untruncated event `E`. -/
theorem stable {ω : ℕ → PoissonPP.Sample (Pt m)} (hg : Good K ω) :
    ∀ᶠ n : ℕ in atTop, (OptFit K n (trunc n ω) ↔ UFit K ω) := by
  obtain ⟨hsupp, hwit⟩ := hg
  choose wp hwp using fun i => (hwit i).1
  choose wm hwm using fun i => (hwit i).2
  have hslab : ∀ p ∈ allPts ω, ∃ k : ℕ, p ∈ PoissonPP.config (ω k).2 ∧
      p.2.1 ∈ Icc (K.a p.1) (K.b p.1) ∧ p.2.2 ∈ Ioc (k : ℝ) (k + 1) := by
    rintro p ⟨k, hk⟩; exact ⟨k, hk, hsupp k p hk⟩
  have w : Wit K wp wm := by
    refine ⟨fun i => (hwp i).2.1, fun i => (hwm i).2.1, fun i => (hwp i).2.2,
      fun i => (hwm i).2.2, fun i => ?_, fun i => ?_, fun i => ?_⟩
    · obtain ⟨k, -, hI, -⟩ := hslab _ (hwp i).1
      rwa [(hwp i).2.1] at hI
    · obtain ⟨k, -, -, hD⟩ := hslab _ (hwp i).1
      exact le_trans (Nat.cast_nonneg k) hD.1.le
    · obtain ⟨k, -, -, hD⟩ := hslab _ (hwm i).1
      exact le_trans (Nat.cast_nonneg k) hD.1.le
  set T := Tstar (K := K) wp wm
  have hDT : ∀ i, (wp i).2.2 ≤ T ∧ (wm i).2.2 ≤ T := by
    intro i
    have hB : 0 ≤ tiltB (K := K) wp wm := by
      unfold tiltB
      exact div_nonneg (mul_nonneg zero_le_two (Finset.sum_nonneg fun j _ =>
        mul_nonneg (Ls_pos K j).le (add_nonneg (w.pD j) (w.mD j)))) (Qs_pos K).le
    have hS : 0 ≤ Sb K := Finset.sum_nonneg fun j _ => by positivity
    have h1 : (wp i).2.2 + (wm i).2.2 ≤ Dsum wp wm :=
      Finset.single_le_sum (f := fun i => (wp i).2.2 + (wm i).2.2)
        (fun j _ => add_nonneg (w.pD j) (w.mD j)) (Finset.mem_univ i)
    have : Dsum wp wm ≤ T := by
      simp only [T, Tstar]; nlinarith
    exact ⟨by linarith [w.mD i], by linarith [w.pD i]⟩
  rw [eventually_atTop]
  refine ⟨⌈T⌉₊ + 1, fun n hn => ?_⟩
  have hnT : T < n := by
    have := Nat.le_ceil T
    have : ((⌈T⌉₊ + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast hn
    push_cast at this
    linarith
  -- points in the first `n` slabs, and the slab of a shallow point
  have hin : ∀ p ∈ allPts ω, p.2.2 ≤ T → p ∈ PoissonPP.config (trunc n ω).2 := by
    intro p hp hpT
    obtain ⟨k, hk, -, hD⟩ := hslab p hp
    rw [mem_config_trunc]
    refine ⟨k, ?_, hk⟩
    have : (k : ℝ) < n := by linarith [hD.1]
    exact_mod_cast this
  have hsub : ∀ p ∈ PoissonPP.config (trunc n ω).2, p ∈ allPts ω := by
    intro p hp
    obtain ⟨k, -, hk⟩ := (mem_config_trunc n ω p).1 hp
    exact ⟨k, hk⟩
  have hwpn : ∀ i, wp i ∈ PoissonPP.config (trunc n ω).2 := fun i =>
    hin _ (hwp i).1 (hDT i).1
  have hwmn : ∀ i, wm i ∈ PoissonPP.config (trunc n ω).2 := fun i =>
    hin _ (hwm i).1 (hDT i).2
  -- a copy with `ε ≤ 0` feasible for the first `n` slabs is feasible for all points
  have hext : ∀ z : Copy, z.1 ≤ 0 → Feasible K (PoissonPP.config (trunc n ω).2) z →
      ∀ p ∈ allPts ω, ¬ violates K z p := by
    intro z hz hf p hp
    by_cases hpT : p.2.2 ≤ T
    · exact hf p (hin p hp hpT)
    · obtain ⟨k, -, hI, -⟩ := hslab p hp
      exact deep_ok w hz (fun i => hf _ (hwpn i)) (fun i => hf _ (hwmn i)) p hI (not_le.mp hpT).le
  have hzero_all : ∀ p ∈ allPts ω, ¬ violates K zeroCopy p := by
    intro p hp
    obtain ⟨k, -, -, hD⟩ := hslab p hp
    exact not_violates_zero (le_trans (Nat.cast_nonneg k) hD.1.le)
  constructor
  · rintro ⟨z, hF, -, hf, hopt⟩
    have hz : z.1 ≤ 0 := hopt zeroCopy fun p hp => hzero_all p (hsub p hp)
    exact ⟨z, hF, hext z hz hf, fun z' hz' => hopt z' fun p hp => hz' p (hsub p hp)⟩
  · rintro ⟨z, hF, hf, hopt⟩
    have hz : z.1 ≤ 0 := hopt zeroCopy hzero_all
    have hfn : Feasible K (PoissonPP.config (trunc n ω).2) z := fun p hp => hf p (hsub p hp)
    refine ⟨z, hF, below_ok w hz (fun i => hfn _ (hwpn i)) (fun i => hfn _ (hwmn i)) hnT.le, hfn,
      fun z' hz' => ?_⟩
    by_cases h' : z'.1 ≤ 0
    · exact hopt z' (hext z' h' hz')
    · linarith [not_le.mp h']

/-! ### Almost surely good -/

variable (K)

/-- Where the points of slab `k` live. -/
def supp (k : ℕ) : Set (Pt m) :=
  {p | p.2.1 ∈ Icc (K.a p.1) (K.b p.1) ∧ p.2.2 ∈ Ioc (k : ℝ) (k + 1)}

omit [NeZero m] in
lemma measurableSet_supp (k : ℕ) : MeasurableSet (supp K k) := by
  have ha : Measurable fun p : Pt m => K.a p.1 := (Measurable.of_discrete).comp measurable_fst
  have hb : Measurable fun p : Pt m => K.b p.1 := (Measurable.of_discrete).comp measurable_fst
  have hs : Measurable fun p : Pt m => p.2.1 := measurable_fst.comp measurable_snd
  have hd : Measurable fun p : Pt m => p.2.2 := measurable_snd.comp measurable_snd
  exact ((measurableSet_le ha hs).inter (measurableSet_le hs hb)).inter
    ((measurableSet_lt measurable_const hd).inter (measurableSet_le hd measurable_const))

omit [NeZero m] in
lemma ΛS_supp_compl (k : ℕ) : ΛS K k (supp K k)ᶜ = 0 := by
  have hm := (measurableSet_supp K k).compl
  unfold ΛS
  rw [Measure.coe_finset_sum, Finset.sum_apply]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [Measure.dirac_prod, Measure.map_apply measurable_prodMk_left hm,
    Measure.restrict_apply (measurable_prodMk_left hm)]
  convert measure_empty (μ := (volume : Measure (ℝ × ℝ)))
  ext q
  simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_compl_iff, supp, Set.mem_setOf_eq,
    Set.mem_prod, mem_empty_iff_false, iff_false, not_and]
  intro h hq
  exact h ⟨hq.1, hq.2⟩

omit [NeZero m] in
lemma ae_supp : ∀ᵐ ω ∂model K, ∀ k, ∀ p ∈ PoissonPP.config (ω k).2, p ∈ supp K k := by
  rw [ae_all_iff]
  intro k
  have hV : MeasurableSet {x : PoissonPP.Sample (Pt m) |
      ∀ p ∈ PoissonPP.config x.2, p ∉ (supp K k)ᶜ} :=
    PoissonPP.measurableSet_sample fun n =>
      PoissonPP.measurable_void_tuple (measurableSet_supp K k).compl n
  have hmap : (model K).map (fun ω => ω k) = PoissonPP.law (ΛS K k) :=
    Measure.infinitePi_map_eval _ k
  have h := (ae_map_iff (measurable_pi_apply k).aemeasurable hV).1 (by
    rw [hmap, ae_iff]
    have hc : {x : PoissonPP.Sample (Pt m) | ¬ ∀ p ∈ PoissonPP.config x.2, p ∉ (supp K k)ᶜ} =
        {x | ∀ p ∈ PoissonPP.config x.2, p ∉ (supp K k)ᶜ}ᶜ := rfl
    rw [hc, prob_compl_eq_one_sub hV, PoissonPP.law_void _ (measurableSet_supp K k).compl,
      ΛS_supp_compl]
    simp)
  filter_upwards [h] with ω hω p hp
  simpa using hω p hp

omit [NeZero m] in
/-- A region with intensity growing linearly in the cutoff is hit almost surely. -/
lemma ae_hits {R : Set (Pt m)} (hR : MeasurableSet R) {c : ℝ} (hc : 0 < c)
    (hΛ : ∀ n : ℕ, ENNReal.ofReal (c * n) ≤ Λ K n R) :
    ∀ᵐ ω ∂model K, ∃ p ∈ allPts ω, p ∈ R := by
  rw [ae_iff]
  set C := {ω : ℕ → PoissonPP.Sample (Pt m) | ¬ ∃ p ∈ allPts ω, p ∈ R}
  have hV : MeasurableSet {x : PoissonPP.Sample (Pt m) | ∀ p ∈ PoissonPP.config x.2, p ∉ R} :=
    PoissonPP.measurableSet_sample fun n => PoissonPP.measurable_void_tuple hR n
  have hfree : LabelFree {x : PoissonPP.Sample (Pt m) | ∀ p ∈ PoissonPP.config x.2, p ∉ R} := by
    intro n x σ
    simp only [Set.mem_setOf_eq, PoissonPP.config_comp_perm]
  have hle : ∀ n : ℕ, model K C ≤ ENNReal.ofReal (Real.exp (-(c * n))) := by
    intro n
    calc model K C ≤ model K {ω | trunc n ω ∈
          {x : PoissonPP.Sample (Pt m) | ∀ p ∈ PoissonPP.config x.2, p ∉ R}} := by
          refine measure_mono fun ω hω p hp hpR => hω ⟨p, ?_, hpR⟩
          obtain ⟨k, -, hk⟩ := (mem_config_trunc n ω p).1 hp
          exact ⟨k, hk⟩
      _ = ENNReal.ofReal (Real.exp (-(Λ K n R).toReal)) := by
          rw [model_trunc K n hV hfree, PoissonPP.law_void _ hR]
      _ ≤ _ := by
          apply ENNReal.ofReal_le_ofReal
          apply Real.exp_le_exp.mpr
          have := (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).1 (hΛ n)
          linarith
  have hlim : Tendsto (fun n : ℕ => ENNReal.ofReal (Real.exp (-(c * n)))) atTop (nhds 0) := by
    rw [← ENNReal.ofReal_zero]
    refine (ENNReal.continuous_ofReal.tendsto 0).comp ?_
    refine Real.tendsto_exp_atBot.comp ?_
    exact tendsto_neg_atTop_atBot.comp
      (tendsto_natCast_atTop_atTop.const_mul_atTop hc)
  exact le_antisymm (ge_of_tendsto' hlim hle) bot_le

omit [NeZero m] in
lemma Λ_ge_single (T : ℝ) (i : Fin m) (S : Set (Pt m)) :
    (volume.restrict (Icc (K.a i) (K.b i) ×ˢ Icc 0 T)) (Prod.mk i ⁻¹' S) ≤ Λ K T S := by
  unfold Λ
  rw [Measure.coe_finset_sum, Finset.sum_apply]
  refine le_trans ?_ (Finset.single_le_sum (f := fun j => ((Measure.dirac j).prod
    (volume.restrict (Icc (K.a j) (K.b j) ×ˢ Icc 0 T))) S) (fun _ _ => bot_le)
    (Finset.mem_univ i))
  rw [Measure.dirac_prod]
  exact Measure.le_map_apply measurable_prodMk_left.aemeasurable S

omit [NeZero m] in
lemma vol_box_le (T : ℝ) (hT : 0 ≤ T) {lo hi : ℝ} (i : Fin m) (S : Set (Pt m))
    (hlo : K.a i ≤ lo) (hhi : hi ≤ K.b i) (hsub : ∀ q : ℝ × ℝ, q.1 ∈ Icc lo hi → (i, q) ∈ S) :
    ENNReal.ofReal ((hi - lo) * T) ≤ Λ K T S := by
  refine le_trans ?_ (Λ_ge_single K T i S)
  rw [Measure.restrict_apply' (measurableSet_Icc.prod measurableSet_Icc)]
  refine le_trans ?_ (measure_mono (s := Icc lo hi ×ˢ Icc 0 T) ?_)
  · rw [Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Icc, Real.volume_Icc, sub_zero]
    rcases le_total lo hi with h | h
    · rw [ENNReal.ofReal_mul (by linarith)]
    · rw [ENNReal.ofReal_of_nonpos (mul_nonpos_of_nonpos_of_nonneg (by linarith) hT)]
      exact bot_le
  · rintro q ⟨hq1, hq2⟩
    exact ⟨hsub q hq1, ⟨le_trans hlo hq1.1, le_trans hq1.2 hhi⟩, hq2⟩

lemma ae_good : ∀ᵐ ω ∂model K, Good K ω := by
  have hc : ∀ i, 0 < min (δK K) (Ls K i) := fun i => lt_min (δK_pos K) (Ls_pos K i)
  have hR : ∀ i, MeasurableSet {p : Pt m | p.1 = i ∧ K.b i - δK K ≤ p.2.1} := fun i =>
    (measurableSet_eq_fun measurable_fst measurable_const).inter
      (measurableSet_le measurable_const (measurable_fst.comp measurable_snd))
  have hL : ∀ i, MeasurableSet {p : Pt m | p.1 = i ∧ p.2.1 ≤ K.a i + δK K} := fun i =>
    (measurableSet_eq_fun measurable_fst measurable_const).inter
      (measurableSet_le (measurable_fst.comp measurable_snd) measurable_const)
  have hright : ∀ i, ∀ᵐ ω ∂model K, ∃ p ∈ allPts ω, p ∈ {p : Pt m | p.1 = i ∧ K.b i - δK K ≤ p.2.1} :=
    fun i => ae_hits K (hR i) (hc i) fun n => by
      have := vol_box_le K n (Nat.cast_nonneg n) i {p : Pt m | p.1 = i ∧ K.b i - δK K ≤ p.2.1}
        (lo := K.b i - min (δK K) (Ls K i)) (hi := K.b i)
        (by have := min_le_right (δK K) (Ls K i); have e : Ls K i = K.b i - K.a i := rfl; linarith)
        le_rfl
        (fun q hq => ⟨rfl, le_trans (by linarith [min_le_left (δK K) (Ls K i)]) hq.1⟩)
      simpa using this
  have hleft : ∀ i, ∀ᵐ ω ∂model K, ∃ p ∈ allPts ω, p ∈ {p : Pt m | p.1 = i ∧ p.2.1 ≤ K.a i + δK K} :=
    fun i => ae_hits K (hL i) (hc i) fun n => by
      have := vol_box_le K n (Nat.cast_nonneg n) i {p : Pt m | p.1 = i ∧ p.2.1 ≤ K.a i + δK K}
        (lo := K.a i) (hi := K.a i + min (δK K) (Ls K i)) le_rfl
        (by have := min_le_right (δK K) (Ls K i); have e : Ls K i = K.b i - K.a i := rfl; linarith)
        (fun q hq => ⟨rfl, le_trans hq.2 (by linarith [min_le_left (δK K) (Ls K i)])⟩)
      simpa using this
  filter_upwards [ae_supp K, ae_all_iff.2 hright, ae_all_iff.2 hleft] with ω h1 h2 h3
  exact ⟨fun k p hp => h1 k p hp, fun i => ⟨h2 i, h3 i⟩⟩

/-! ### The limit model without truncation -/

omit [NeZero m] in
lemma LabelFree.union {A B : Set (PoissonPP.Sample (Pt m))} (hA : LabelFree A) (hB : LabelFree B) :
    LabelFree (A ∪ B) := fun n x σ => by
  simp only [Set.mem_union, hA n x σ, hB n x σ]

omit [NeZero m] in
lemma LabelFree.iUnion {ι : Sort*} {A : ι → Set (PoissonPP.Sample (Pt m))}
    (hA : ∀ i, LabelFree (A i)) : LabelFree (⋃ i, A i) := fun n x σ => by
  simp only [Set.mem_iUnion, hA _ n x σ]

/-- The candidate events at cutoff `T`. -/
def candG (T : ℝ) : Set (PoissonPP.Sample (Pt m)) :=
  {ω | HasVertexCandidate K T ω} ∪ ⋃ p ∈ parPairs K, {ω | HasSegCand K p.1 p.2 T ω}

/-- The null events of the classification. -/
def nullG : Set (PoissonPP.Sample (Pt m)) :=
  ({ω | BadExtra K (vertexCopy K) ω} ∪ {ω | BadP (Opp2 K) ω} ∪ {ω | BadP (Tri3 K) ω}) ∪
    ⋃ p : Fin m × Fin m, {ω | BadExtra K (segBase K p.1 p.2) ω}

omit [NeZero m] in
lemma measurableSet_candG (T : ℝ) : MeasurableSet (candG K T) :=
  (measurableSet_HasVertexCandidate K T).union
    (Finset.measurableSet_biUnion _ fun p _ => measurableSet_HasSegCand K p.1 p.2 T)

omit [NeZero m] in
lemma measurableSet_nullG : MeasurableSet (nullG K) :=
  (((measurableSet_BadExtra K _ (measurable_vertexCopy K)).union
    (measurableSet_BadP (measurableSet_Opp2 (K := K)))).union
      (measurableSet_BadP (measurableSet_Tri3 (K := K)))).union
    (MeasurableSet.iUnion fun p => measurableSet_BadExtra K _ (measurable_segBase K p.1 p.2))

omit [NeZero m] in
lemma labelFree_candG (T : ℝ) : LabelFree (candG K T) :=
  (labelFree_vertex K T).union (LabelFree.iUnion fun p => LabelFree.iUnion fun _ =>
    labelFree_seg K p.1 p.2 T)

omit [NeZero m] in
lemma labelFree_nullG : LabelFree (nullG K) :=
  (((labelFree_badExtra K _).union (labelFree_badP _)).union (labelFree_badP _)).union
    (LabelFree.iUnion fun p => labelFree_badExtra K _)

variable {K}

omit [NeZero m] in
lemma candG_sub (hG : GoodSides K) (T : ℝ) : candG K T ⊆ {ω | OptFit K T ω} := by
  rintro ω (h | h)
  · exact optFit_of_vertex K T ω h
  · obtain ⟨p, hp, hk⟩ := mem_iUnion₂.mp h
    exact optFit_of_seg K (hG.parPair (Finset.mem_filter.mp hp).2) T ω hk

omit [NeZero m] in
lemma optFit_sub (hG : GoodSides K) (T : ℝ) : {ω | OptFit K T ω} ⊆ candG K T ∪ nullG K := by
  intro ω h
  rcases general_classify hG T ω h with hV | ⟨k, kb, hu, hk⟩ | hO | hT
  · exact Or.inl (Or.inl hV)
  · exact Or.inl (Or.inr (mem_iUnion₂.mpr ⟨(k, kb), Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, hu⟩, hk⟩))
  · exact Or.inr (Or.inl (Or.inl (Or.inr hO)))
  · exact Or.inr (Or.inl (Or.inr hT))

/-- **The paper's event `E` in the untruncated model.** For a polygon with `GoodSides`, the
probability that some copy optimal for all the points of the infinite strips fits equals the
Theorem 8 value: vertex term plus segment terms. -/
theorem untruncated_prob (hG : GoodSides K) :
    model K {ω | UFit K ω} = spatialVertexIntegral K * coneVertexDensity K +
      ∑ p ∈ parPairs K, segDensity K p.1 p.2 * ∫⁻ v, chordWeightInf K p.1 v := by
  set A : ℕ → Set (ℕ → PoissonPP.Sample (Pt m)) := fun n => {ω | trunc n ω ∈ candG K n}
  have hAm : ∀ n, MeasurableSet (A n) := fun n =>
    (measurableSet_candG K n).preimage (measurable_trunc n)
  have hA : ∀ n : ℕ, model K (A n) = PoissonPP.law (Λ K n) {ω | OptFit K n ω} := by
    intro n
    rw [model_trunc K n (measurableSet_candG K n) (labelFree_candG K n)]
    apply le_antisymm (measure_mono (candG_sub hG n))
    calc PoissonPP.law (Λ K n) {ω | OptFit K n ω}
        ≤ PoissonPP.law (Λ K n) (candG K n ∪ nullG K) := measure_mono (optFit_sub hG n)
      _ ≤ PoissonPP.law (Λ K n) (candG K n) + PoissonPP.law (Λ K n) (nullG K) :=
          measure_union_le _ _
      _ = _ := by rw [nullG, general_null_zero K n, add_zero]
  have hlim := general_optFit_limit hG
  simp_rw [← hA] at hlim
  have hnull : ∀ᵐ ω ∂model K, ∀ n : ℕ, trunc n ω ∉ nullG K := by
    rw [ae_all_iff]
    intro n
    rw [ae_iff]
    simp only [not_not]
    rw [model_trunc K n (measurableSet_nullG K) (labelFree_nullG K), nullG, general_null_zero K n]
  have hev : ∀ᵐ ω ∂model K, ∀ᶠ n : ℕ in atTop, (ω ∈ A n ↔ UFit K ω) := by
    filter_upwards [ae_good K, hnull] with ω hg hn
    refine (stable hg).mono fun n h => ?_
    rw [← h]
    constructor
    · intro hω; exact candG_sub hG n hω
    · intro hω
      rcases optFit_sub hG n hω with h' | h'
      · exact h'
      · exact absurd h' (hn n)
  set Alim : Set (ℕ → PoissonPP.Sample (Pt m)) := ⋃ N : ℕ, ⋂ n ≥ N, A n
  have hAlimm : MeasurableSet Alim :=
    MeasurableSet.iUnion fun N => MeasurableSet.iInter fun n => MeasurableSet.iInter fun _ => hAm n
  have hAlim : ∀ᵐ ω ∂model K, (ω ∈ Alim ↔ UFit K ω) := by
    filter_upwards [hev] with ω h
    obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp h
    constructor
    · intro hω
      obtain ⟨N, hN⟩ := mem_iUnion.mp hω
      have := mem_iInter₂.mp hN (max N N₀) (le_max_left _ _)
      exact (hN₀ _ (le_max_right _ _)).1 this
    · intro hU
      exact mem_iUnion.mpr ⟨N₀, mem_iInter₂.mpr fun n hn => (hN₀ n hn).2 hU⟩
  have h2 : Tendsto (fun n => model K (A n)) atTop (nhds (model K Alim)) :=
    tendsto_measure_of_ae_tendsto_indicator_of_isFiniteMeasure atTop hAlimm hAm (by
      filter_upwards [hev, hAlim] with ω h1 h3
      exact h1.mono fun n h => h.trans h3.symm)
  rw [← tendsto_nhds_unique h2 hlim]
  exact measure_congr (Filter.eventuallyEq_set.2 (hAlim.mono fun ω h => h.symm))

/-- **Corollary 2 in the untruncated model**: a counterclockwise triangle of area one. -/
theorem untruncated_triangle {w : Fin 3 → ℝ × ℝ} (harea : area w = 1) :
    let K := sidesOf w (le_refl 3) (convexPos_triangle (by rw [harea]; norm_num)) harea
    model K {ω | UFit K ω} = ENNReal.ofReal (ptri (len w 0 ^ 2) (len w 1 ^ 2) (len w 2 ^ 2)) := by
  intro K
  have hG := goodSides_of_convex (le_refl 3) (convexPos_triangle (by rw [harea]; norm_num)) harea
  rw [untruncated_prob hG]
  exact tendsto_nhds_unique (general_optFit_limit hG) (triangle_vertices_optFit_limit harea)

/-- **The equilateral triangle in the untruncated model: `P(E) = 13/48`.** -/
theorem untruncated_equilateral : model eqTri {ω | UFit eqTri ω} = ENNReal.ofReal (13 / 48) := by
  rw [untruncated_prob eqTri_good]
  exact tendsto_nhds_unique (general_optFit_limit eqTri_good) equilateral_optFit_limit

end Enclosing
