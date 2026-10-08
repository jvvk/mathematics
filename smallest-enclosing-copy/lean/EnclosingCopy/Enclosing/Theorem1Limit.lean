import EnclosingCopy.Enclosing.Theorem1Events

/-!
# Theorem 1: the limit event and the truncated model

On the witness event, the box limit event `EvF` is the truncated-model event `OptFit` at any
cutoff `T ≥ T₀(M)` (`evF_iff_optFit`). Witnesses fail with probability at most
`2m e^{-cM}`, uniformly in `T ≥ M` (`witness_fail_le`). Hence `P_T(EvF)` is within that of the
Theorem 8 value for large `T`.
-/

namespace Enclosing
open MeasureTheory Set Filter Topology

variable {m : ℕ} (K : Sides m)

/-- A depth threshold for the witnesses: `Tstar ≤ T₀(M)`. -/
noncomputable def T0 (M : ℝ) : ℝ := 2 * (4 * M * per K / Qs K) * Sb K + 2 * m * M

variable [NeZero m]

lemma tstar_le {wp wm : Fin m → Pt m} (w : Wit K wp wm) {M : ℝ}
    (hp : ∀ i, (wp i).2.2 ≤ M) (hm : ∀ i, (wm i).2.2 ≤ M) : Tstar (K := K) wp wm ≤ T0 K M := by
  have hQ := Qs_pos K
  have hper := per_pos K
  have hS : 0 ≤ Sb K := Finset.sum_nonneg fun i _ => by positivity
  have hM : 0 ≤ M := le_trans (w.pD 0) (hp 0)
  have hB : tiltB (K := K) wp wm ≤ 4 * M * per K / Qs K := by
    unfold tiltB
    apply div_le_div_of_nonneg_right _ hQ.le
    have hs : ∑ i, Ls K i * ((wp i).2.2 + (wm i).2.2) ≤ ∑ i, Ls K i * (2 * M) :=
      Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left
        (by linarith [hp i, hm i]) (Ls_pos K i).le
    have he : ∑ i, Ls K i * (2 * M) = 2 * M * per K := by
      rw [per, Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
    linarith
  have hD : Dsum wp wm ≤ 2 * m * M := by
    unfold Dsum
    calc ∑ i, ((wp i).2.2 + (wm i).2.2) ≤ ∑ _i : Fin m, 2 * M :=
          Finset.sum_le_sum fun i _ => by linarith [hp i, hm i]
      _ = 2 * m * M := by simp; ring
  unfold Tstar T0
  nlinarith

/-- **On the witness event the box limit event is `OptFit`.** -/
theorem evF_iff_optFit {M R T : ℝ} (hR : 0 ≤ R)
    (hbox : ∀ wp wm : Fin m → Pt m, Wit K wp wm → (∀ i, (wp i).2.2 ≤ M) →
      (∀ i, (wm i).2.2 ≤ M) → ∀ z : Copy, z.1 ≤ 0 → (∀ i, ¬ violates K z (wp i)) →
        (∀ i, ¬ violates K z (wm i)) → z ∈ copyBox R)
    (hT : T0 K M ≤ T) (ω : PoissonPP.Sample (Pt m))
    (hdep : ∀ p ∈ PoissonPP.config ω.2, 0 ≤ p.2.2) (hw : WitEv K M (PoissonPP.config ω.2)) :
    EvF K R M (PoissonPP.config ω.2) ↔ OptFit K T ω := by
  set μ := PoissonPP.config ω.2
  obtain ⟨wp, wm, hW, hmem, hdM⟩ := witEv_wit K hw
  have h0f : Feasible K μ zeroCopy := fun p hp => not_violates_zero (hdep p hp)
  have h0b : zeroCopy ∈ copyBox R := by simp [copyBox, zeroCopy, hR]
  have hinbox : ∀ z, Feasible K μ z → z.1 ≤ 0 → z ∈ copyBox R := fun z hz hz0 =>
    hbox wp wm hW (fun i => (hdM i).1) (fun i => (hdM i).2) z hz0
      (fun i => hz _ (hmem i).1) (fun i => hz _ (hmem i).2)
  constructor
  · rintro ⟨-, z, hzb, hzf, hzF, hzm⟩
    have hz0 : z.1 ≤ 0 := hzm zeroCopy h0b h0f
    refine ⟨z, hzF, below_ok hW hz0 (fun i => hzf _ (hmem i).1) (fun i => hzf _ (hmem i).2)
      ((tstar_le K hW (fun i => (hdM i).1) (fun i => (hdM i).2)).trans hT), hzf, ?_⟩
    intro z' hz'
    by_contra hlt
    push Not at hlt
    exact absurd (hzm z' (hinbox z' hz' (by linarith)) hz') (not_le.mpr hlt)
  · rintro ⟨z, hzF, -, hzf, hzm⟩
    have hz0 : z.1 ≤ 0 := hzm zeroCopy h0f
    exact ⟨hw, z, hinbox z hzf hz0, hzf, hzF, fun y hyb hyf => hzm y hyf⟩

omit [NeZero m] in
lemma vol_box_le_depth {T M : ℝ} (hM : 0 ≤ M) (hMT : M ≤ T) {lo hi : ℝ} (i : Fin m)
    (S : Set (Pt m)) (hlo : K.a i ≤ lo) (hhi : hi ≤ K.b i)
    (hsub : ∀ q : ℝ × ℝ, q.1 ∈ Icc lo hi → q.2 ∈ Icc 0 M → (i, q) ∈ S) :
    ENNReal.ofReal ((hi - lo) * M) ≤ Λ K T S := by
  refine le_trans ?_ (Λ_ge_single K T i S)
  rw [Measure.restrict_apply' (measurableSet_Icc.prod measurableSet_Icc)]
  refine le_trans ?_ (measure_mono (s := Icc lo hi ×ˢ Icc 0 M) ?_)
  · rw [Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Icc, Real.volume_Icc, sub_zero]
    rcases le_total lo hi with h | h
    · rw [ENNReal.ofReal_mul (by linarith)]
    · rw [ENNReal.ofReal_of_nonpos (mul_nonpos_of_nonpos_of_nonneg (by linarith) hM)]
      exact bot_le
  · rintro q ⟨hq1, hq2⟩
    exact ⟨hsub q hq1 hq2, ⟨le_trans hlo hq1.1, le_trans hq1.2 hhi⟩, hq2.1, le_trans hq2.2 hMT⟩

omit [NeZero m] in
/-- The void probability of a region of intensity at least `c M`. -/
lemma law_void_le (T : ℝ) {S : Set (Pt m)} (hS : MeasurableSet S) {x : ℝ}
    (hx : ENNReal.ofReal x ≤ Λ K T S) :
    PoissonPP.law (Λ K T) {ω | ∀ p ∈ PoissonPP.config ω.2, p ∉ S} ≤
      ENNReal.ofReal (Real.exp (-x)) := by
  rw [PoissonPP.law_void _ hS]
  apply ENNReal.ofReal_le_ofReal
  apply Real.exp_le_exp.mpr
  by_cases hx0 : x ≤ 0
  · have : 0 ≤ (Λ K T S).toReal := ENNReal.toReal_nonneg
    linarith
  · have := (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).1 hx
    linarith

/-- **Witnesses fail with exponentially small probability**, uniformly in the cutoff. -/
theorem witness_fail_le {M T : ℝ} (hM : 0 ≤ M) (hMT : M ≤ T) :
    PoissonPP.law (Λ K T) {ω | ¬ WitEv K M (PoissonPP.config ω.2)} ≤
      ∑ i : Fin m, 2 * ENNReal.ofReal (Real.exp (-(min (δK K) (Ls K i) * M))) := by
  have hs : Measurable fun p : Pt m => p.2.1 := measurable_fst.comp measurable_snd
  have hd : Measurable fun p : Pt m => p.2.2 := measurable_snd.comp measurable_snd
  have hWPm : ∀ i, MeasurableSet {p : Pt m | WP K M i p} := fun i =>
    (measurableSet_eq_fun measurable_fst measurable_const).inter
      ((measurableSet_le measurable_const hs).inter
        ((measurableSet_Icc.preimage hs).inter
          ((measurableSet_le measurable_const hd).inter (measurableSet_le hd measurable_const))))
  have hWMm : ∀ i, MeasurableSet {p : Pt m | WM K M i p} := fun i =>
    (measurableSet_eq_fun measurable_fst measurable_const).inter
      ((measurableSet_le hs measurable_const).inter
        ((measurableSet_le measurable_const hd).inter (measurableSet_le hd measurable_const)))
  have hsub : {ω : PoissonPP.Sample (Pt m) | ¬ WitEv K M (PoissonPP.config ω.2)} ⊆
      ⋃ i, ({ω | ∀ p ∈ PoissonPP.config ω.2, p ∉ {p | WP K M i p}} ∪
        {ω | ∀ p ∈ PoissonPP.config ω.2, p ∉ {p | WM K M i p}}) := by
    intro ω hω
    simp only [WitEv, not_forall, not_and_or, not_exists] at hω
    obtain ⟨i, h | h⟩ := hω
    · exact mem_iUnion.mpr ⟨i, Or.inl fun p hp hW => (h p).elim (· hp) (· hW)⟩
    · exact mem_iUnion.mpr ⟨i, Or.inr fun p hp hW => (h p).elim (· hp) (· hW)⟩
  refine (measure_mono hsub).trans ((measure_iUnion_fintype_le _ _).trans
    (Finset.sum_le_sum fun i _ => ?_))
  have hc := lt_min (δK_pos K) (Ls_pos K i)
  have hL : Ls K i = K.b i - K.a i := rfl
  have h1 : ENNReal.ofReal (min (δK K) (Ls K i) * M) ≤ Λ K T {p | WP K M i p} := by
    have := vol_box_le_depth K hM hMT i {p | WP K M i p}
      (lo := K.b i - min (δK K) (Ls K i)) (hi := K.b i)
      (by have := min_le_right (δK K) (Ls K i); linarith) le_rfl
      (fun q hq hq2 => ⟨rfl, le_trans (by linarith [min_le_left (δK K) (Ls K i)]) hq.1,
        ⟨by have := min_le_right (δK K) (Ls K i); linarith [hq.1], hq.2⟩, hq2.1, hq2.2⟩)
    simpa using this
  have h2 : ENNReal.ofReal (min (δK K) (Ls K i) * M) ≤ Λ K T {p | WM K M i p} := by
    have := vol_box_le_depth K hM hMT i {p | WM K M i p}
      (lo := K.a i) (hi := K.a i + min (δK K) (Ls K i)) le_rfl
      (by have := min_le_right (δK K) (Ls K i); linarith)
      (fun q hq hq2 => ⟨rfl, le_trans hq.2 (by linarith [min_le_left (δK K) (Ls K i)]),
        hq2.1, hq2.2⟩)
    simpa using this
  rw [two_mul]
  exact (measure_union_le _ _).trans (add_le_add (law_void_le K T (hWPm i) h1)
    (law_void_le K T (hWMm i) h2))

end Enclosing
