import EnclosingCopy.Enclosing.Theorem1Strict
import EnclosingCopy.Enclosing.VaryingBoundaryLimit
import EnclosingCopy.Enclosing.BoundaryFeasible

/-!
# Theorem 1: the events and their almost-sure stabilisation in the Poisson model

* `measurableSet_optFit`: "some minimiser of a continuous objective over a compact feasible set
  lies in a closed set" is measurable when feasibility is closed jointly in the data and the
  copy. It is the intersection over rational `t` of `{min ≤ t} → {fit min ≤ t}`, and each of
  these sets is the projection of a closed set along a compact factor.
-/

namespace Enclosing
open MeasureTheory Set Filter Topology

/-- Projection of a closed set along a compact factor is closed. -/
lemma isClosed_exists_mem_compact {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {C : Set Y} (hC : IsCompact C) {S : Set (X × Y)} (hS : IsClosed S) :
    IsClosed {x | ∃ y ∈ C, (x, y) ∈ S} := by
  have : CompactSpace C := isCompact_iff_compactSpace.mp hC
  have hS' : IsClosed {p : X × C | (p.1, (p.2 : Y)) ∈ S} :=
    hS.preimage (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
  have h := isClosedMap_fst_of_compactSpace _ hS'
  convert h using 1
  ext x
  simp only [mem_setOf_eq, mem_image, Prod.exists, exists_and_right, exists_eq_right]
  constructor
  · rintro ⟨y, hy, hxy⟩; exact ⟨⟨y, hy⟩, hxy⟩
  · rintro ⟨⟨y, hy⟩, hxy⟩; exact ⟨y, hy, hxy⟩

/-- **Measurability of "some minimiser fits".** -/
theorem measurableSet_optFit {X Y : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] [TopologicalSpace Y] {C : Set Y} (hC : IsCompact C)
    {P : X → Y → Prop} (hP : IsClosed {p : X × Y | P p.1 p.2}) {Fit : Set Y}
    (hFit : IsClosed Fit) {f : Y → ℝ} (hf : Continuous f) :
    MeasurableSet {x | ∃ z ∈ C, P x z ∧ z ∈ Fit ∧ ∀ y ∈ C, P x y → f z ≤ f y} := by
  let A : ℚ → Set X := fun t => {x | ∃ y ∈ C, (x, y) ∈ {p : X × Y | P p.1 p.2 ∧ f p.2 ≤ t}}
  let B : ℚ → Set X := fun t => {x | ∃ y ∈ C,
    (x, y) ∈ {p : X × Y | P p.1 p.2 ∧ p.2 ∈ Fit ∧ f p.2 ≤ t}}
  let B₀ : Set X := {x | ∃ y ∈ C, (x, y) ∈ {p : X × Y | P p.1 p.2 ∧ p.2 ∈ Fit}}
  have hA : ∀ t, IsClosed (A t) := fun t => isClosed_exists_mem_compact hC
    (hP.inter (isClosed_le (hf.comp continuous_snd) continuous_const))
  have hB : ∀ t, IsClosed (B t) := fun t => isClosed_exists_mem_compact hC
    (hP.inter ((hFit.preimage continuous_snd).inter
      (isClosed_le (hf.comp continuous_snd) continuous_const)))
  have hB₀ : IsClosed B₀ := isClosed_exists_mem_compact hC (hP.inter (hFit.preimage continuous_snd))
  have heq : {x | ∃ z ∈ C, P x z ∧ z ∈ Fit ∧ ∀ y ∈ C, P x y → f z ≤ f y} =
      B₀ ∩ ⋂ t : ℚ, ((A t)ᶜ ∪ B t) := by
    ext x
    simp only [mem_setOf_eq, mem_inter_iff, mem_iInter, mem_union, mem_compl_iff, A, B, B₀]
    constructor
    · rintro ⟨z, hzC, hPz, hzF, hmin⟩
      refine ⟨⟨z, hzC, hPz, hzF⟩, fun t => ?_⟩
      by_cases ht : ∃ y ∈ C, P x y ∧ f y ≤ t
      · obtain ⟨y, hyC, hPy, hy⟩ := ht
        exact Or.inr ⟨z, hzC, hPz, hzF, (hmin y hyC hPy).trans hy⟩
      · exact Or.inl ht
    · rintro ⟨⟨z₁, hz₁C, hPz₁, hz₁F⟩, hall⟩
      have hclosedx : IsClosed {y | P x y} :=
        hP.preimage (continuous_const.prodMk continuous_id)
      have hFx : IsCompact (C ∩ {y | P x y}) := hC.inter_right hclosedx
      have hGx : IsCompact (C ∩ ({y | P x y} ∩ Fit)) := hC.inter_right (hclosedx.inter hFit)
      obtain ⟨y₀, ⟨hy₀C, hPy₀⟩, hy₀min⟩ :=
        hFx.exists_isMinOn ⟨z₁, hz₁C, hPz₁⟩ hf.continuousOn
      obtain ⟨z₀, ⟨hz₀C, hPz₀, hz₀F⟩, hz₀min⟩ :=
        hGx.exists_isMinOn ⟨z₁, hz₁C, hPz₁, hz₁F⟩ hf.continuousOn
      refine ⟨z₀, hz₀C, hPz₀, hz₀F, fun y hyC hPy => ?_⟩
      by_contra hlt
      push Not at hlt
      have hV : f y₀ < f z₀ := lt_of_le_of_lt (hy₀min ⟨hyC, hPy⟩) hlt
      obtain ⟨t, ht1, ht2⟩ := exists_rat_btwn hV
      rcases hall t with h | ⟨z, hzC, hPz, hzF, hz⟩
      · exact h ⟨y₀, hy₀C, hPy₀, ht1.le⟩
      · have := hz₀min ⟨hzC, hPz, hzF⟩
        simp only [mem_setOf_eq] at this
        linarith
  rw [heq]
  exact hB₀.measurableSet.inter (MeasurableSet.iInter fun t =>
    (hA t).measurableSet.compl.union (hB t).measurableSet)

variable {m : ℕ} (K : Sides m)

/-! ### The events -/

/-- A witness near the right end of side `i`, at depth at most `M`. -/
def WP (M : ℝ) (i : Fin m) (p : Pt m) : Prop :=
  p.1 = i ∧ K.b i - δK K ≤ p.2.1 ∧ p.2.1 ∈ Icc (K.a i) (K.b i) ∧ 0 ≤ p.2.2 ∧ p.2.2 ≤ M

/-- A witness near the left end of side `i`, at depth at most `M`. -/
def WM (M : ℝ) (i : Fin m) (p : Pt m) : Prop :=
  p.1 = i ∧ p.2.1 ≤ K.a i + δK K ∧ 0 ≤ p.2.2 ∧ p.2.2 ≤ M

/-- Every side has witnesses near both ends. -/
def WitEv (M : ℝ) (μ : Multiset (Pt m)) : Prop :=
  ∀ i, (∃ p ∈ μ, WP K M i p) ∧ (∃ p ∈ μ, WM K M i p)

/-- **The finite-`n` event**: some copy in the box `R`, minimising the physical scale among the
feasible copies of the box, fits physically. -/
def EvN (R M : ℝ) (n : ℕ) (μ : Multiset (Pt m)) : Prop :=
  WitEv K M μ ∧ ∃ z ∈ copyBox R, Feasible K μ z ∧ TangentFits K (1 / n) z ∧
    ∀ y ∈ copyBox R, Feasible K μ y → tangentScale (1 / n) z ≤ tangentScale (1 / n) y

/-- **The limit event**: some LP-optimal copy of the box fits. -/
def EvF (R M : ℝ) (μ : Multiset (Pt m)) : Prop :=
  WitEv K M μ ∧ ∃ z ∈ copyBox R, Feasible K μ z ∧ Fits K z ∧
    ∀ y ∈ copyBox R, Feasible K μ y → z.1 ≤ y.1

lemma witEv_wit {M : ℝ} {μ : Multiset (Pt m)} (h : WitEv K M μ) :
    ∃ wp wm : Fin m → Pt m, Wit K wp wm ∧ (∀ i, wp i ∈ μ ∧ wm i ∈ μ) ∧
      ∀ i, (wp i).2.2 ≤ M ∧ (wm i).2.2 ≤ M := by
  choose wp hwp using fun i => (h i).1
  choose wm hwm using fun i => (h i).2
  exact ⟨wp, wm, ⟨fun i => (hwp i).2.1, fun i => (hwm i).2.1, fun i => (hwp i).2.2.1,
    fun i => (hwm i).2.2.1, fun i => (hwp i).2.2.2.1, fun i => (hwp i).2.2.2.2.1,
    fun i => (hwm i).2.2.2.1⟩, fun i => ⟨(hwp i).1, (hwm i).1⟩,
    fun i => ⟨(hwp i).2.2.2.2.2, (hwm i).2.2.2.2⟩⟩

/-! ### Measurability -/

lemma continuous_side_val {X : Type*} [TopologicalSpace X] {g : X → Pt m} (hg : Continuous g)
    (F : Fin m → ℝ) : Continuous fun x => F (g x).1 :=
  (continuous_of_discreteTopology (f := F)).comp (continuous_fst.comp hg)

lemma isClosed_feasible_tuple (k : ℕ) :
    IsClosed {p : (Fin k → Pt m) × Copy | ∀ j, ¬ violates K p.2 (p.1 j)} := by
  have e : {p : (Fin k → Pt m) × Copy | ∀ j, ¬ violates K p.2 (p.1 j)} =
      ⋂ j, {p : (Fin k → Pt m) × Copy | ¬ violates K p.2 (p.1 j)} := by ext; simp
  rw [e]
  refine isClosed_iInter fun j => ?_
  have hx : Continuous fun p : (Fin k → Pt m) × Copy => p.1 j :=
    (continuous_apply j).comp continuous_fst
  have hH : Continuous fun p : (Fin k → Pt m) × Copy => Hs K p.2 (p.1 j).1 := by
    have h1 := continuous_side_val hx K.h
    have h2 := continuous_side_val hx (fun i => (K.u i).1)
    have h3 := continuous_side_val hx (fun i => (K.u i).2)
    simp only [Hs, dot]
    fun_prop
  have hs : Continuous fun p : (Fin k → Pt m) × Copy => (p.1 j).2.1 := by fun_prop
  have hd : Continuous fun p : (Fin k → Pt m) × Copy => (p.1 j).2.2 := by fun_prop
  have : {p : (Fin k → Pt m) × Copy | ¬ violates K p.2 (p.1 j)} =
      {p | p.2.2.2 * (p.1 j).2.1 - Hs K p.2 (p.1 j).1 ≤ (p.1 j).2.2} := by
    ext p; simp [violates]
  rw [this]
  exact isClosed_le (((continuous_snd.snd.snd).mul hs).sub hH) hd

lemma isClosed_fits : IsClosed {z : Copy | Fits K z} := by
  have e : {z : Copy | Fits K z} =
      ⋂ i, {z : Copy | Hs K z i ≤ min (z.2.2 * K.a i) (z.2.2 * K.b i)} := by
    ext z; simp [Fits]
  rw [e]
  refine isClosed_iInter fun i => isClosed_le ?_ ?_
  · unfold Hs dot; fun_prop
  · fun_prop

lemma isClosed_tangentFits (q : ℝ) : IsClosed {z : Copy | TangentFits K q z} := by
  have e : {z : Copy | TangentFits K q z} = ⋂ i, ({z : Copy | 0 ≤ tangentFitSlack K q z i (K.a i)} ∩
      {z : Copy | 0 ≤ tangentFitSlack K q z i (K.b i)}) := by
    ext z; simp [TangentFits]
  rw [e]
  have hc : ∀ i s, Continuous fun z : Copy => tangentFitSlack K q z i s := fun i s =>
    (continuous_tangentFitSlack K i s).comp (continuous_const.prodMk continuous_id)
  exact isClosed_iInter fun i =>
    (isClosed_le continuous_const (hc i _)).inter (isClosed_le continuous_const (hc i _))

lemma continuous_tangentScale (q : ℝ) : Continuous (tangentScale q) := by
  unfold tangentScale
  refine Continuous.div (by fun_prop) (by fun_prop) fun z => ?_
  exact (Real.sqrt_pos.2 (by positivity)).ne'

lemma measurableSet_witEv (M : ℝ) (k : ℕ) :
    MeasurableSet {x : Fin k → Pt m | WitEv K M (PoissonPP.config x)} := by
  have e0 : {x : Fin k → Pt m | WitEv K M (PoissonPP.config x)} =
      ⋂ i, ({x : Fin k → Pt m | ∃ p, (∃ j, x j = p) ∧ WP K M i p} ∩
        {x : Fin k → Pt m | ∃ p, (∃ j, x j = p) ∧ WM K M i p}) := by
    ext x; simp [WitEv, PoissonPP.mem_config]
  rw [e0]
  refine MeasurableSet.iInter fun i => ?_
  have hWP : MeasurableSet {p : Pt m | WP K M i p} := by
    have hs : Measurable fun p : Pt m => p.2.1 := measurable_fst.comp measurable_snd
    have hd : Measurable fun p : Pt m => p.2.2 := measurable_snd.comp measurable_snd
    exact (measurableSet_eq_fun measurable_fst measurable_const).inter
      ((measurableSet_le measurable_const hs).inter
        ((measurableSet_Icc.preimage hs).inter
          ((measurableSet_le measurable_const hd).inter (measurableSet_le hd measurable_const))))
  have hWM : MeasurableSet {p : Pt m | WM K M i p} := by
    have hs : Measurable fun p : Pt m => p.2.1 := measurable_fst.comp measurable_snd
    have hd : Measurable fun p : Pt m => p.2.2 := measurable_snd.comp measurable_snd
    exact (measurableSet_eq_fun measurable_fst measurable_const).inter
      ((measurableSet_le hs measurable_const).inter
        ((measurableSet_le measurable_const hd).inter (measurableSet_le hd measurable_const)))
  have e1 : {x : Fin k → Pt m | ∃ p, (∃ j, x j = p) ∧ WP K M i p} =
      ⋃ j, (fun x : Fin k → Pt m => x j) ⁻¹' {p | WP K M i p} := by
    ext x; simp only [mem_setOf_eq, mem_iUnion, mem_preimage]
    constructor
    · rintro ⟨p, ⟨j, rfl⟩, hp⟩; exact ⟨j, hp⟩
    · rintro ⟨j, hj⟩; exact ⟨_, ⟨j, rfl⟩, hj⟩
  have e2 : {x : Fin k → Pt m | ∃ p, (∃ j, x j = p) ∧ WM K M i p} =
      ⋃ j, (fun x : Fin k → Pt m => x j) ⁻¹' {p | WM K M i p} := by
    ext x; simp only [mem_setOf_eq, mem_iUnion, mem_preimage]
    constructor
    · rintro ⟨p, ⟨j, rfl⟩, hp⟩; exact ⟨j, hp⟩
    · rintro ⟨j, hj⟩; exact ⟨_, ⟨j, rfl⟩, hj⟩
  rw [e1, e2]
  exact (MeasurableSet.iUnion fun j => hWP.preimage (measurable_pi_apply j)).inter
    (MeasurableSet.iUnion fun j => hWM.preimage (measurable_pi_apply j))

lemma feasible_config_tuple {k : ℕ} (x : Fin k → Pt m) (z : Copy) :
    Feasible K (PoissonPP.config x) z ↔ ∀ j, ¬ violates K z (x j) := by
  simp only [Feasible, PoissonPP.mem_config]
  constructor
  · intro h j; exact h _ ⟨j, rfl⟩
  · rintro h p ⟨j, rfl⟩; exact h j

theorem measurableSet_evN (R M : ℝ) (n k : ℕ) :
    MeasurableSet {x : Fin k → Pt m | EvN K R M n (PoissonPP.config x)} := by
  have h := measurableSet_optFit (P := fun (x : Fin k → Pt m) z => ∀ j, ¬ violates K z (x j))
    (isCompact_copyBox R) (isClosed_feasible_tuple K k) (isClosed_tangentFits K (1 / n)) (continuous_tangentScale (1 / n))
  have e : {x : Fin k → Pt m | EvN K R M n (PoissonPP.config x)} =
      {x | WitEv K M (PoissonPP.config x)} ∩ {x | ∃ z ∈ copyBox R, (∀ j, ¬ violates K z (x j)) ∧
        z ∈ {z | TangentFits K (1 / n) z} ∧ ∀ y ∈ copyBox R, (∀ j, ¬ violates K y (x j)) →
          tangentScale (1 / n) z ≤ tangentScale (1 / n) y} := by
    ext x; simp only [EvN, mem_setOf_eq, mem_inter_iff, feasible_config_tuple]
  rw [e]
  exact (measurableSet_witEv K M k).inter h

theorem measurableSet_evF (R M : ℝ) (k : ℕ) :
    MeasurableSet {x : Fin k → Pt m | EvF K R M (PoissonPP.config x)} := by
  have h := measurableSet_optFit (P := fun (x : Fin k → Pt m) z => ∀ j, ¬ violates K z (x j))
    (isCompact_copyBox R) (isClosed_feasible_tuple K k) (isClosed_fits K) (continuous_fst : Continuous fun z : Copy => z.1)
  have e : {x : Fin k → Pt m | EvF K R M (PoissonPP.config x)} =
      {x | WitEv K M (PoissonPP.config x)} ∩ {x | ∃ z ∈ copyBox R, (∀ j, ¬ violates K z (x j)) ∧
        z ∈ {z | Fits K z} ∧ ∀ y ∈ copyBox R, (∀ j, ¬ violates K y (x j)) → z.1 ≤ y.1} := by
    ext x; simp only [EvF, mem_setOf_eq, mem_inter_iff, feasible_config_tuple]
  rw [e]
  exact (measurableSet_witEv K M k).inter h

/-! ### Almost-sure stabilisation in the Poisson model -/

lemma Λ_negDepth (T : ℝ) : Λ K T {p : Pt m | p.2.2 < 0} = 0 := by
  have hm : MeasurableSet {p : Pt m | p.2.2 < 0} :=
    measurableSet_lt (measurable_snd.comp measurable_snd) measurable_const
  unfold Λ
  rw [Measure.coe_finsetSum, Finset.sum_apply]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [Measure.dirac_prod, Measure.map_apply measurable_prodMk_left hm,
    Measure.restrict_apply (measurable_prodMk_left hm)]
  convert measure_empty (μ := (volume : Measure (ℝ × ℝ)))
  ext q
  simp only [mem_inter_iff, mem_preimage, mem_setOf_eq, mem_prod, mem_Icc,
    mem_empty_iff_false, iff_false, not_and]
  intro h _ h0
  linarith

lemma ae_depth_nonneg (T : ℝ) :
    ∀ᵐ ω ∂PoissonPP.law (Λ K T), ∀ p ∈ PoissonPP.config ω.2, 0 ≤ p.2.2 := by
  have hB : MeasurableSet {p : Pt m | p.2.2 < 0} :=
    measurableSet_lt (measurable_snd.comp measurable_snd) measurable_const
  have hV : MeasurableSet {x : PoissonPP.Sample (Pt m) |
      ∀ p ∈ PoissonPP.config x.2, p ∉ {p : Pt m | p.2.2 < 0}} :=
    PoissonPP.measurableSet_sample fun n => PoissonPP.measurable_void_tuple hB n
  rw [ae_iff]
  have hc : {x : PoissonPP.Sample (Pt m) | ¬ ∀ p ∈ PoissonPP.config x.2, 0 ≤ p.2.2} =
      {x | ∀ p ∈ PoissonPP.config x.2, p ∉ {p : Pt m | p.2.2 < 0}}ᶜ := by
    ext x; simp [not_le]
  rw [hc, prob_compl_eq_one_sub hV, PoissonPP.law_void _ hB, Λ_negDepth]
  simp

lemma isClosed_feasible (μ : Multiset (Pt m)) : IsClosed {z : Copy | Feasible K μ z} := by
  have e : {z : Copy | Feasible K μ z} = ⋂ p ∈ μ, {z : Copy | ¬ violates K z p} := by
    ext z; simp [Feasible]
  rw [e]
  refine isClosed_biInter fun p _ => ?_
  have : {z : Copy | ¬ violates K z p} = {z | z.2.2 * p.2.1 - Hs K z p.1 ≤ p.2.2} := by
    ext z; simp [violates]
  rw [this]
  exact isClosed_le (by unfold Hs dot; fun_prop) continuous_const

/-- **Almost-sure stabilisation.** In the Poisson model at any cutoff, for almost every
configuration the finite-`n` event and the limit event eventually agree. -/
theorem poisson_stable (hG : GoodSides K) {M R : ℝ} (hR : 0 ≤ R)
    (hbox : ∀ wp wm : Fin m → Pt m, Wit K wp wm → (∀ i, (wp i).2.2 ≤ M) →
      (∀ i, (wm i).2.2 ≤ M) → ∀ z : Copy, z.1 ≤ 0 → (∀ i, ¬ violates K z (wp i)) →
        (∀ i, ¬ violates K z (wm i)) → z ∈ copyBox R) (T : ℝ) :
    ∀ᵐ ω ∂PoissonPP.law (Λ K T), ∀ᶠ n : ℕ in atTop,
      (EvN K R M n (PoissonPP.config ω.2) ↔ EvF K R M (PoissonPP.config ω.2)) := by
  filter_upwards [nonDeg_ae hG T, ae_depth_nonneg K T] with ω hnd hdep
  obtain ⟨N, y⟩ := ω
  set μ := PoissonPP.config y
  by_cases hw : WitEv K M μ
  swap
  · exact Eventually.of_forall fun n => iff_of_false (fun h => hw h.1) (fun h => hw h.1)
  obtain ⟨wp, wm, hW, hmem, hdM⟩ := witEv_wit K hw
  let G : Set Copy := {z | z ∈ copyBox R ∧ Feasible K μ z}
  have hGc : IsCompact G := (isCompact_copyBox R).inter_right (isClosed_feasible K μ)
  have h0 : zeroCopy ∈ G := by
    refine ⟨by simp [copyBox, zeroCopy, hR], fun p hp => not_violates_zero (hdep p hp)⟩
  obtain ⟨zs, hzsG, hzsmin⟩ := hGc.exists_isMinOn ⟨zeroCopy, h0⟩ continuous_fst.continuousOn
  have hmin : ∀ z ∈ G, zs.1 ≤ z.1 := fun z hz => hzsmin hz
  have hzs0 : zs.1 ≤ 0 := hmin zeroCopy h0
  have hinbox : ∀ z, Feasible K μ z → z.1 ≤ 0 → z ∈ copyBox R := fun z hz hz0 =>
    hbox wp wm hW (fun i => (hdM i).1) (fun i => (hdM i).2) z hz0
      (fun i => hz _ (hmem i).1) (fun i => hz _ (hmem i).2)
  have hglob : ∀ z', Feasible K μ z' → zs.1 ≤ z'.1 := by
    intro z' hz'
    by_contra hlt
    push Not at hlt
    exact absurd (hmin z' ⟨hinbox z' hz' (by linarith), hz'⟩) (not_le.mpr hlt)
  obtain ⟨D, hD, hgap⟩ := optimum_tilt_gap K hG y zs hzsG.2 hglob hnd.1 hnd.2.1
  have hS : IsCompact {z ∈ G | z.1 = zs.1} :=
    hGc.inter_right (isClosed_eq continuous_fst continuous_const)
  have hstrict : (∃ z ∈ G, z.1 = zs.1 ∧ Fits K z) →
      ∃ z ∈ G, z.1 = zs.1 ∧ ∀ i, Hs K z i < min (z.2.2 * K.a i) (z.2.2 * K.b i) := by
    rintro ⟨z, hzG, hz1, hzF⟩
    obtain ⟨z', hz'f, hz'1, hz's⟩ := strict_rep hG y hnd zs hglob ⟨z, hzG.2, hz1, hzF⟩
    exact ⟨z', ⟨hinbox z' hz'f (by rw [hz'1]; exact hzs0), hz'f⟩, hz'1, hz's⟩
  have hst := tangent_enclosing_event_stability K G zs hzsG hR hD
    (fun z hz => (hz.1.2.2.2)) hmin (fun z hz => hgap z hz.2) hS hstrict
  refine hst.mono fun n h => ?_
  constructor
  · rintro ⟨-, z, hzb, hzf, hzt, hzm⟩
    have := h.1 ⟨z, ⟨hzb, hzf⟩, hzt, fun y' hy' => hzm y' hy'.1 hy'.2⟩
    obtain ⟨z', hz'G, hz'1, hz'F⟩ := this
    exact ⟨hw, z', hz'G.1, hz'G.2, hz'F, fun y' hyb hyf => hz'1 ▸ hmin y' ⟨hyb, hyf⟩⟩
  · rintro ⟨-, z, hzb, hzf, hzF, hzm⟩
    have hz1 : z.1 = zs.1 := le_antisymm (hzm zs hzsG.1 hzsG.2) (hmin z ⟨hzb, hzf⟩)
    obtain ⟨z', hz'G, hz't, hz'm⟩ := h.2 ⟨z, ⟨hzb, hzf⟩, hz1, hzF⟩
    exact ⟨hw, z', hz'G.1, hz'G.2, hz't, fun y' hyb hyf => hz'm y' ⟨hyb, hyf⟩⟩

end Enclosing
