import EnclosingCopy.Enclosing.Theorem1Physical
import EnclosingCopy.Enclosing.Untruncated
import EnclosingCopy.Enclosing.PolygonWitnesses
import EnclosingCopy.Enclosing.PolygonOverlap

/-!
# Theorem 1

For a convex polygon of area one (vertices `v` counterclockwise in strictly convex position) and
`n` independent uniform points in it, the probability that some smallest similar copy containing
the points lies in the polygon tends to the Theorem 8 value, which is the probability of the
event `E` of the limit model (`theorem1`, `theorem1_model`).

The good event (`good_prob`): sample points lie in the polygon, none in a corner overlap,
witnesses in windows near both ends of every side, and a finite `δ/2`-net of the polygon is
hit. On it the event is the windowed finite event (`trueEv_iff_evN`); that converges to the
Poisson limit event (Codex's `polygon_boundary_varying_event_limit` with `poisson_stable`), which
is within the witness failure probability of `OptFit` at cutoff `T` (`evF_iff_optFit`), whose
probability tends to the Theorem 8 value as `T → ∞` (`general_optFit_limit`).
-/

namespace Enclosing
open MeasureTheory Set Filter Topology Real Metric

variable {m : ℕ} [NeZero m]

/-! ### Witness windows give witness marks -/

/-- The witness windows of side `i`: near the right end (`true`) and the left end (`false`). -/
noncomputable def winHalf (K : Sides m) (i : Fin m) : ℝ := min (δK K) (Ls K i) / 2

noncomputable def winA (K : Sides m) (t : Fin m × Bool) : ℝ :=
  if t.2 then K.b t.1 - winHalf K t.1 else K.a t.1 + winHalf K t.1 / 2

noncomputable def winB (K : Sides m) (t : Fin m × Bool) : ℝ :=
  if t.2 then K.b t.1 - winHalf K t.1 / 2 else K.a t.1 + winHalf K t.1

lemma winHalf_pos (K : Sides m) (i : Fin m) : 0 < winHalf K i :=
  half_pos (lt_min (δK_pos K) (Ls_pos K i))

lemma winHalf_le (K : Sides m) (i : Fin m) : winHalf K i ≤ δK K / 2 ∧ winHalf K i ≤ Ls K i / 2 :=
  ⟨by unfold winHalf; linarith [min_le_left (δK K) (Ls K i)],
    by unfold winHalf; linarith [min_le_right (δK K) (Ls K i)]⟩

lemma win_bounds (K : Sides m) (t : Fin m × Bool) :
    K.a t.1 < winA K t ∧ winA K t < winB K t ∧ winB K t < K.b t.1 := by
  have hp := winHalf_pos K t.1
  have hl := (winHalf_le K t.1).2
  have hL : Ls K t.1 = K.b t.1 - K.a t.1 := rfl
  unfold winA winB
  split_ifs <;> exact ⟨by linarith, by linarith, by linarith⟩

/-- A sample point in a witness window, in no corner overlap, gives a witness mark. -/
lemma witEv_of_windows (K : Sides m) (hG : GoodSides K) {T M y : ℝ} {n : ℕ} (hn : 0 < n)
    (hyT : y ≤ T) (hyM : y ≤ M) {x : Fin n → ℝ × ℝ} (hx : ∀ j, x j ∈ polygonRegion K)
    (hcorner : ∀ j, x j ∉ cornerOverlap K (T / n))
    (hw : ∀ t, ∃ j, x j ∈ sideWindow K t.1 (winA K t) (winB K t) (y / n)) :
    WitEv K M (winMarks K T n x) := by
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hmark : ∀ t, ∃ p ∈ winMarks K T n x, p.1 = t.1 ∧ p.2.1 ∈ Icc (winA K t) (winB K t) ∧
      0 ≤ p.2.2 ∧ p.2.2 ≤ y := by
    intro t
    obtain ⟨j, hj⟩ := hw t
    obtain ⟨⟨s, d⟩, ⟨hs, hd⟩, hxj⟩ := hj
    have hco := sideCoords_chart (K.u t.1) (hG.unit t.1) (K.h t.1) (s, d)
    rw [hxj] at hco
    have hs' : dot (x j) (sideTangent (K.u t.1)) = s := congrArg Prod.fst hco
    have hd' : K.h t.1 - dot (x j) (K.u t.1) = d := congrArg Prod.snd hco
    have hstrip : x j ∈ physicalSideStrip K t.1 (T / n) := by
      refine ⟨hx j, ?_⟩
      show K.h t.1 - dot (x j) (K.u t.1) ∈ Icc 0 (T / n)
      rw [hd']
      exact ⟨hd.1, hd.2.trans (div_le_div_of_nonneg_right hyT hnr.le)⟩
    refine ⟨physicalBoundaryMark K T n (x j), ?_, ?_⟩
    · apply Multiset.mem_map.mpr
      refine ⟨x j, ?_, rfl⟩
      simp only [PoissonPP.inWindow, Multiset.mem_filter]
      exact ⟨(PoissonPP.mem_config x _).mpr ⟨j, rfl⟩, mem_iUnion.mpr ⟨t.1, hstrip⟩⟩
    · rw [physicalBoundaryMark_eq_tangentPointMark K hn hstrip (hcorner j)]
      simp only [tangentPointMark]
      refine ⟨trivial, by rw [hs']; exact hs, ?_, ?_⟩
      · rw [hd']; exact div_nonneg hd.1 (by positivity)
      · rw [hd', div_le_iff₀ (by positivity)]
        calc d ≤ y / n := hd.2
          _ = y * (1 / n) := by ring
  intro i
  have hδ := (winHalf_le K i).1
  have hp := winHalf_pos K i
  have hL : Ls K i = K.b i - K.a i := rfl
  constructor
  · obtain ⟨p, hp', hside, hs, hd0, hdy⟩ := hmark (i, true)
    refine ⟨p, hp', hside, ?_, ⟨?_, ?_⟩, hd0, hdy.trans hyM⟩
    · simp only [winA, ite_true] at hs; linarith [hs.1, δK_pos K]
    · simp only [winA, ite_true] at hs; linarith [hs.1, (winHalf_le K i).2]
    · simp only [winB, ite_true] at hs; linarith [hs.2]
  · obtain ⟨p, hp', hside, hs, hd0, hdy⟩ := hmark (i, false)
    refine ⟨p, hp', hside, ?_, hd0, hdy.trans hyM⟩
    simp only [winB] at hs; simp at hs; linarith [hs.2, δK_pos K]

/-! ### A finite net of the polygon -/

lemma exists_net (K : Sides m) (hG : GoodSides K) (hv1 : volume (polygonRegion K) = 1)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ Y : Finset (ℝ × ℝ), (∀ y ∈ Y, 0 < volume (polygonRegion K ∩ ball y (δ / 2))) ∧
      ∀ {k : ℕ} (x : Fin k → ℝ × ℝ), (∀ y ∈ Y, ∃ j, x j ∈ polygonRegion K ∩ ball y (δ / 2)) →
        polygonRegion K ⊆ ⋃ s ∈ range x, closedBall s δ := by
  set P := polygonRegion K
  obtain ⟨t, htP, htf, hcov⟩ :=
    finite_cover_balls_of_compact (isCompact_polygonRegion K hG) (half_pos hδ)
  have hint := interior_nonempty_of_volume_pos (convex_polygonRegion K) (by rw [hv1]; exact one_pos)
  have hcl : closure (interior P) = P := by
    rw [(convex_polygonRegion K).closure_interior_eq_closure_of_nonempty_interior hint,
      (isClosed_polygonRegion K).closure_eq]
  refine ⟨htf.toFinset, fun y hy => ?_, fun x hx z hz => ?_⟩
  · have hyP : y ∈ P := htP (htf.mem_toFinset.mp hy)
    have hy' : y ∈ closure (interior P) := by rw [hcl]; exact hyP
    obtain ⟨w, hw, hwy⟩ := Metric.mem_closure_iff.mp hy' (δ / 2) (half_pos hδ)
    have hU : IsOpen (interior P ∩ ball y (δ / 2)) := isOpen_interior.inter isOpen_ball
    have hpos := hU.measure_pos volume ⟨w, hw, by rw [mem_ball, dist_comm]; exact hwy⟩
    exact lt_of_lt_of_le hpos (measure_mono (inter_subset_inter_left _ interior_subset))
  · obtain ⟨y, hy, hzy⟩ := mem_iUnion₂.mp (hcov hz)
    obtain ⟨j, -, hj⟩ := hx y (htf.mem_toFinset.mpr hy)
    refine mem_iUnion₂.mpr ⟨x j, mem_range_self j, ?_⟩
    rw [mem_closedBall]
    have h1 := mem_ball.mp hzy
    have h2 := mem_ball.mp hj
    calc dist z (x j) ≤ dist z y + dist y (x j) := dist_triangle _ _ _
      _ ≤ δ / 2 + δ / 2 := by rw [dist_comm y]; linarith
      _ = δ := by ring

/-! ### `candG` and `OptFit` have the same probability -/

lemma law_candG (K : Sides m) (hG : GoodSides K) (T : ℝ) :
    PoissonPP.law (Λ K T) (candG K T) = PoissonPP.law (Λ K T) {ω | OptFit K T ω} := by
  apply le_antisymm (measure_mono (candG_sub hG T))
  calc PoissonPP.law (Λ K T) {ω | OptFit K T ω}
      ≤ PoissonPP.law (Λ K T) (candG K T ∪ nullG K) := measure_mono (optFit_sub hG T)
    _ ≤ PoissonPP.law (Λ K T) (candG K T) + PoissonPP.law (Λ K T) (nullG K) :=
        measure_union_le _ _
    _ = _ := by rw [nullG, general_null_zero K T, add_zero]

/-- **The box limit event and `candG` differ by at most the witness failure.** -/
lemma evF_candG_close (K : Sides m) (hG : GoodSides K) {M R T : ℝ} (hR : 0 ≤ R)
    (hbox : ∀ wp wm : Fin m → Pt m, Wit K wp wm → (∀ i, (wp i).2.2 ≤ M) →
      (∀ i, (wm i).2.2 ≤ M) → ∀ z : Copy, z.1 ≤ 0 → (∀ i, ¬ violates K z (wp i)) →
        (∀ i, ¬ violates K z (wm i)) → z ∈ copyBox R) (hT : T0 K M ≤ T) :
    PoissonPP.law (Λ K T) {ω | EvF K R M (PoissonPP.config ω.2)} ≤
        PoissonPP.law (Λ K T) (candG K T) +
          PoissonPP.law (Λ K T) {ω | ¬ WitEv K M (PoissonPP.config ω.2)} ∧
      PoissonPP.law (Λ K T) (candG K T) ≤
        PoissonPP.law (Λ K T) {ω | EvF K R M (PoissonPP.config ω.2)} +
          PoissonPP.law (Λ K T) {ω | ¬ WitEv K M (PoissonPP.config ω.2)} := by
  set μ := PoissonPP.law (Λ K T)
  set D := {ω : PoissonPP.Sample (Pt m) | ¬ ∀ p ∈ PoissonPP.config ω.2, 0 ≤ p.2.2}
  have hD : μ D = 0 := by
    have := ae_depth_nonneg K T
    rw [ae_iff] at this; exact this
  have hN : μ (nullG K) = 0 := by rw [nullG, general_null_zero K T]
  set W := {ω : PoissonPP.Sample (Pt m) | ¬ WitEv K M (PoissonPP.config ω.2)}
  have key : ∀ ω, ω ∉ D → ω ∉ nullG K → ω ∉ W →
      (EvF K R M (PoissonPP.config ω.2) ↔ ω ∈ candG K T) := by
    intro ω hd hn hw
    simp only [D, W, mem_setOf_eq, not_not] at hd hw
    rw [evF_iff_optFit K hR hbox hT ω hd hw]
    constructor
    · intro h
      rcases optFit_sub hG T h with h' | h'
      · exact h'
      · exact absurd h' hn
    · intro h; exact candG_sub hG T h
  constructor
  · calc μ {ω | EvF K R M (PoissonPP.config ω.2)} ≤ μ (candG K T ∪ (W ∪ (D ∪ nullG K))) := by
          apply measure_mono
          intro ω hω
          by_cases hw : ω ∈ W; · exact Or.inr (Or.inl hw)
          by_cases hd : ω ∈ D; · exact Or.inr (Or.inr (Or.inl hd))
          by_cases hn : ω ∈ nullG K; · exact Or.inr (Or.inr (Or.inr hn))
          exact Or.inl ((key ω hd hn hw).1 hω)
      _ ≤ μ (candG K T) + μ W := by
          refine (measure_union_le _ _).trans (add_le_add le_rfl ?_)
          refine (measure_union_le _ _).trans ?_
          rw [measure_union_null hD hN, add_zero]
  · calc μ (candG K T) ≤ μ ({ω | EvF K R M (PoissonPP.config ω.2)} ∪ (W ∪ (D ∪ nullG K))) := by
          apply measure_mono
          intro ω hω
          by_cases hw : ω ∈ W; · exact Or.inr (Or.inl hw)
          by_cases hd : ω ∈ D; · exact Or.inr (Or.inr (Or.inl hd))
          by_cases hn : ω ∈ nullG K; · exact Or.inr (Or.inr (Or.inr hn))
          exact Or.inl ((key ω hd hn hw).2 hω)
      _ ≤ μ {ω | EvF K R M (PoissonPP.config ω.2)} + μ W := by
          refine (measure_union_le _ _).trans (add_le_add le_rfl ?_)
          refine (measure_union_le _ _).trans ?_
          rw [measure_union_null hD hN, add_zero]

/-! ### The good event has high probability -/

section Probabilities

variable {v : Fin m → ℝ × ℝ} (hm : 3 ≤ m) (hv : ConvexPos v) (harea : area v = 1)

lemma outside_null (n : ℕ) :
    (Measure.pi fun _ : Fin n => polygonSample v hm hv harea)
      {x | ∃ j, x j ∈ (polygonRegion (sidesOf v hm hv harea))ᶜ} = 0 := by
  apply nonpos_iff_eq_zero.mp
  refine (PoissonPP.iid_hit_le _ (measurableSet_polygonRegion _).compl n).trans (le_of_eq ?_)
  rw [polygonSample_eq_volume_restrict hm hv harea,
    Measure.restrict_apply (measurableSet_polygonRegion _).compl, compl_inter_self,
    measure_empty, mul_zero]

lemma net_fail_limit {δ : ℝ} (Y : Finset (ℝ × ℝ))
    (hY : ∀ y ∈ Y, 0 < volume (polygonRegion (sidesOf v hm hv harea) ∩ ball y (δ / 2))) :
    Tendsto (fun n : ℕ => (Measure.pi fun _ : Fin n => polygonSample v hm hv harea)
      {x | ∃ y ∈ Y, ∀ j, x j ∉ polygonRegion (sidesOf v hm hv harea) ∩ ball y (δ / 2)})
      atTop (𝓝 0) := by
  set P := polygonRegion (sidesOf v hm hv harea)
  have hB : ∀ y : ℝ × ℝ, MeasurableSet (P ∩ ball y (δ / 2)) := fun y =>
    (measurableSet_polygonRegion _).inter measurableSet_ball
  have hp : ∀ y ∈ Y, polygonSample v hm hv harea (P ∩ ball y (δ / 2)) ≠ 0 := by
    intro y hy
    rw [polygonSample_eq_volume_restrict hm hv harea, Measure.restrict_apply (hB y),
      inter_comm, ← inter_assoc, inter_self]
    exact (hY y hy).ne'
  have hlim : ∀ y ∈ Y, Tendsto (fun n : ℕ =>
      (1 - polygonSample v hm hv harea (P ∩ ball y (δ / 2))) ^ n) atTop (𝓝 0) := fun y hy =>
    ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one
      (ENNReal.sub_lt_self ENNReal.one_ne_top one_ne_zero (hp y hy))
  have hsum := tendsto_finsetSum Y hlim
  rw [Finset.sum_const_zero] at hsum
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum (fun n => bot_le)
    fun n => ?_
  have hsub : {x : Fin n → ℝ × ℝ | ∃ y ∈ Y, ∀ j, x j ∉ P ∩ ball y (δ / 2)} ⊆
      ⋃ y ∈ Y, {x | ∀ j, x j ∉ P ∩ ball y (δ / 2)} := by
    intro x ⟨y, hy, h⟩; exact mem_iUnion₂.mpr ⟨y, hy, h⟩
  refine (measure_mono hsub).trans ((measure_biUnion_finset_le _ _).trans (le_of_eq ?_))
  refine Finset.sum_congr rfl fun y _ => ?_
  exact PoissonPP.iid_void_prob _ (hB y) n

end Probabilities

/-! ### Theorem 1 -/

/-- **Theorem 1.** For `n` independent uniform points in a convex polygon of area one, the
probability that some smallest similar copy containing them lies in the polygon tends to the
Theorem 8 value: the vertex term plus the segment terms. -/
theorem theorem1 {v : Fin m → ℝ × ℝ} (hm : 3 ≤ m) (hv : ConvexPos v) (harea : area v = 1) :
    let K := sidesOf v hm hv harea
    Tendsto (fun n : ℕ => (Measure.pi fun _ : Fin n => polygonSample v hm hv harea)
        {x | TrueEv K x}) atTop
      (𝓝 (spatialVertexIntegral K * coneVertexDensity K +
        ∑ p ∈ parPairs K, segDensity K p.1 p.2 * ∫⁻ w, chordWeightInf K p.1 w)) := by
  intro K
  have hG : GoodSides K := goodSides_of_convex hm hv harea
  have hv1 : volume (polygonRegion K) = 1 := polygonRegion_volume_one hm hv harea
  set L := spatialVertexIntegral K * coneVertexDensity K +
    ∑ p ∈ parPairs K, segDensity K p.1 p.2 * ∫⁻ w, chordWeightInf K p.1 w
  have hLim : Tendsto (fun n : ℕ => PoissonPP.law (Λ K n) (candG K n)) atTop (𝓝 L) := by
    simp_rw [law_candG K hG]; exact general_optFit_limit hG
  have hL1 : L ≤ 1 := le_of_tendsto' hLim fun n => prob_le_one
  have hLtop : L ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hL1
  rw [← ENNReal.tendsto_toReal_iff (fun n => measure_ne_top _ _) hLtop, Metric.tendsto_atTop]
  intro ε hε
  set e := ε / 6
  have he : 0 < e := by positivity
  -- witness windows for the sample
  have hWt : ∀ ε > 0, ∃ y > 0, ∀ᶠ n : ℕ in atTop,
      (Measure.pi fun _ : Fin n => polygonSample v hm hv harea).real
        (witnessFailure K (fun t : Fin m × Bool => t.1) (winA K) (winB K) n y) < ε :=
    polygon_witness_tightness hm hv harea (fun t : Fin m × Bool => t.1) (winA K) (winB K)
      (fun t => (win_bounds K t).1) (fun t => (win_bounds K t).2.1) (fun t => (win_bounds K t).2.2)
  obtain ⟨y, hy, hwitn⟩ := hWt e he
  -- witnesses in the model
  have hexp : Tendsto (fun M : ℝ => ∑ i : Fin m, 2 * Real.exp (-(min (δK K) (Ls K i) * M)))
      atTop (𝓝 0) := by
    have hi : ∀ i : Fin m, Tendsto (fun M : ℝ => 2 * Real.exp (-(min (δK K) (Ls K i) * M)))
        atTop (𝓝 0) := by
      intro i
      have hc := lt_min (δK_pos K) (Ls_pos K i)
      have h := Real.tendsto_exp_atBot.comp
        (tendsto_neg_atTop_atBot.comp (tendsto_id.const_mul_atTop hc))
      simpa [Function.comp_def] using h.const_mul 2
    simpa using tendsto_finsetSum Finset.univ fun i _ => hi i
  obtain ⟨M, hMy, hMe⟩ :=
    ((eventually_ge_atTop (max y 0)).and (hexp.eventually (Iio_mem_nhds he))).exists
  have hM : 0 ≤ M := le_trans (le_max_right _ _) hMy
  have hyM : y ≤ M := le_trans (le_max_left _ _) hMy
  -- the box
  obtain ⟨ρF, hρF, hF⟩ := finite_tangent_copy_bound K hG hM
  obtain ⟨ρM, hρM, hMb⟩ := model_copy_bound K hG hM
  set R := max ρF ρM
  have hR : 0 ≤ R := le_trans hρF (le_max_left _ _)
  have hboxF : ∀ wp wm : Fin m → Pt m, Wit K wp wm → (∀ i, (wp i).2.2 ≤ M) →
      (∀ i, (wm i).2.2 ≤ M) → ∀ q : ℝ, 0 < q → q ≤ 1 → ∀ z : Copy,
        tangentScale q z ≤ 1 → |q * z.2.2| ≤ Qs K / 4 →
        (∀ i, ¬ violates K z (wp i)) → (∀ i, ¬ violates K z (wm i)) → z ∈ copyBox R := by
    intro wp wm hW hp hmm q hq hq1 z hs ht hpv hmv
    obtain ⟨h1, h2, h3, h4⟩ := hF wp wm hW hp hmm q hq hq1 z hs ht hpv hmv
    exact ⟨h1.trans (le_max_left _ _), h2.trans (le_max_left _ _), h3.trans (le_max_left _ _),
      h4.trans (le_max_left _ _)⟩
  have hboxM : ∀ wp wm : Fin m → Pt m, Wit K wp wm → (∀ i, (wp i).2.2 ≤ M) →
      (∀ i, (wm i).2.2 ≤ M) → ∀ z : Copy, z.1 ≤ 0 → (∀ i, ¬ violates K z (wp i)) →
        (∀ i, ¬ violates K z (wm i)) → z ∈ copyBox R := by
    intro wp wm hW hp hmm z hz hpv hmv
    obtain ⟨h1, h2, h3, h4⟩ := hMb wp wm hW hp hmm z hz hpv hmv
    exact ⟨h1.trans (le_max_right _ _), h2.trans (le_max_right _ _),
      h3.trans (le_max_right _ _), h4.trans (le_max_right _ _)⟩
  -- fit radius, angle window, net
  obtain ⟨r, hr, hfit⟩ : ∃ r > 0, ∀ q > 0, ∀ z : Copy, 0 < 1 + q * z.1 → |q * z.2.2| ≤ r →
      (tangentCopyRegion K q z ⊆ polygonRegion K ↔ TangentFits K q z) :=
    exists_tangent_fit_radius hm hv harea
  have hmin0 : 0 < min r (Qs K / 4) := lt_min hr (by have := Qs_pos K; positivity)
  set η := arctan (min r (Qs K / 4))
  have hη : 0 < η := arctan_pos.mpr hmin0
  have hηπ : η < π / 2 := arctan_lt_pi_div_two _
  have htanη : tan η = min r (Qs K / 4) := tan_arctan _
  obtain ⟨δ, hδ, hstep0⟩ := step0_sample K hG hv1 hη
  obtain ⟨Y, hYpos, hYnet⟩ := exists_net K hG hv1 hδ
  -- the cutoff
  obtain ⟨Tc, -, hline⟩ := exists_boundary_feasibility_cutoff K hG R
  have hLr : Tendsto (fun n : ℕ => (PoissonPP.law (Λ K n) (candG K n)).toReal) atTop
      (𝓝 L.toReal) := (ENNReal.tendsto_toReal_iff (fun n => measure_ne_top _ _) hLtop).2 hLim
  obtain ⟨Tn, hTn1, hTn2⟩ := ((eventually_ge_atTop
    (⌈max (max Tc (T0 K M)) (max M y)⌉₊ + 1)).and (hLr.eventually (Metric.ball_mem_nhds _ he))).exists
  set T : ℝ := (Tn : ℝ)
  have hTbig : max (max Tc (T0 K M)) (max M y) < T := by
    have h1 := Nat.le_ceil (max (max Tc (T0 K M)) (max M y))
    have h2 : ((⌈max (max Tc (T0 K M)) (max M y)⌉₊ + 1 : ℕ) : ℝ) ≤ T := Nat.cast_le.mpr hTn1
    push_cast at h2; linarith
  have hTc : Tc ≤ T := by linarith [le_max_left Tc (T0 K M), le_max_left (max Tc (T0 K M)) (max M y)]
  have hT0 : T0 K M ≤ T := by
    linarith [le_max_right Tc (T0 K M), le_max_left (max Tc (T0 K M)) (max M y)]
  have hTM : M ≤ T := by linarith [le_max_left M y, le_max_right (max Tc (T0 K M)) (max M y)]
  have hyT : y ≤ T := le_trans hyM hTM
  have hTpos : 0 < T := by
    have : 0 ≤ max (max Tc (T0 K M)) (max M y) :=
      le_trans (le_trans hM (le_max_left M y)) (le_max_right _ _)
    linarith
  have hline' : ∀ x ∈ polygonRegion K, ∀ z ∈ copyBox R, ∀ i,
      z.2.2 * dot x (sideTangent (K.u i)) - Hs K z i ≤ T := fun x hx z hz i =>
    (hline x hx z hz i).trans hTc
  -- the model at cutoff `T`
  have hstable := poisson_stable K hG hR hboxM T
  have hbridge := polygon_boundary_varying_event_limit hm hv harea hTpos
    (fun n μ => EvN K R M n μ) (EvF K R M) (fun n k => measurableSet_evN K R M n k)
    (fun k => measurableSet_evF K R M k) hstable
  obtain ⟨hc1, hc2⟩ := evF_candG_close K hG hR hboxM hT0
  have hwf := witness_fail_le K hM hTM
  set pF := (PoissonPP.law (Λ K T)).real {ω | EvF K R M (PoissonPP.config ω.2)}
  set pC := (PoissonPP.law (Λ K T) (candG K T)).toReal
  set pW := (PoissonPP.law (Λ K T) {ω | ¬ WitEv K M (PoissonPP.config ω.2)}).toReal
  have hpW : pW < e := by
    have h := ENNReal.toReal_mono (by
      exact ENNReal.sum_ne_top.2 fun i _ => ENNReal.mul_ne_top (by simp) ENNReal.ofReal_ne_top) hwf
    rw [ENNReal.toReal_sum (fun i _ => ENNReal.mul_ne_top (by simp) ENNReal.ofReal_ne_top)] at h
    simp only [ENNReal.toReal_mul, ENNReal.toReal_ofNat,
      ENNReal.toReal_ofReal (Real.exp_pos _).le] at h
    exact lt_of_le_of_lt h hMe
  have hFC : |pF - pC| ≤ pW := by
    have h1 := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨measure_ne_top _ _, measure_ne_top _ _⟩) hc1
    have h2 := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨measure_ne_top _ _, measure_ne_top _ _⟩) hc2
    rw [ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)] at h1 h2
    rw [abs_le]; constructor <;> simp only [pF, pC, pW, measureReal_def] at h1 h2 ⊢ <;> linarith
  have hCL : |pC - L.toReal| < e := by
    have := hTn2; rw [Real.dist_eq] at this; exact this
  -- the sample side, eventually in `n`
  have hcorner := cornerOverlap_hit_limit_zero hm hv harea hTpos.le
  have hnet := net_fail_limit hm hv harea Y hYpos
  have hq0 : Tendsto (fun n : ℕ => (1 / (n : ℝ)) * R) atTop (𝓝 0) := by
    simpa using (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ)).mul_const R
  have hev : ∀ᶠ n : ℕ in atTop, 0 < n ∧ (1 / (n : ℝ)) * R < 1 ∧ (1 / (n : ℝ)) * R ≤ r ∧
      (Measure.pi fun _ : Fin n => polygonSample v hm hv harea)
        {x | ∃ j, x j ∈ cornerOverlap K (T / n)} < ENNReal.ofReal e ∧
      (Measure.pi fun _ : Fin n => polygonSample v hm hv harea).real
        (witnessFailure K (fun t : Fin m × Bool => t.1) (winA K) (winB K) n y) < e ∧
      (Measure.pi fun _ : Fin n => polygonSample v hm hv harea)
        {x | ∃ y ∈ Y, ∀ j, x j ∉ polygonRegion K ∩ ball y (δ / 2)} < ENNReal.ofReal e ∧
      |(Measure.pi fun _ : Fin n => polygonSample v hm hv harea).real
        {x | EvN K R M n ((PoissonPP.inWindow (physicalBoundaryWindow K T n)
          (PoissonPP.config x)).map (physicalBoundaryMark K T n))} - pF| < e := by
    have hpos : ∀ᶠ n : ℕ in atTop, 0 < n := eventually_gt_atTop 0
    have h1 := hq0.eventually (Iio_mem_nhds one_pos)
    have h2 := hq0.eventually (Iic_mem_nhds hr)
    have h3 := hcorner.eventually (Iio_mem_nhds (ENNReal.ofReal_pos.2 he))
    have h4 := hnet.eventually (Iio_mem_nhds (ENNReal.ofReal_pos.2 he))
    have h5 := hbridge.eventually (Metric.ball_mem_nhds pF he)
    filter_upwards [hpos, h1, h2, h3, hwitn, h4, h5] with n a1 a2 a3 a4 a5 a6 a7
    exact ⟨a1, a2, a3, a4, a5, a6, by rw [Real.dist_eq] at a7; exact a7⟩
  obtain ⟨N, hN⟩ := eventually_atTop.1 hev
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨hn0, hqR, hrR, hcor, hwit, hnf, hBF⟩ := hN n hn
  set μ := Measure.pi fun _ : Fin n => polygonSample v hm hv harea
  set A := {x : Fin n → ℝ × ℝ | TrueEv K x}
  set B := {x : Fin n → ℝ × ℝ | EvN K R M n ((PoissonPP.inWindow (physicalBoundaryWindow K T n)
    (PoissonPP.config x)).map (physicalBoundaryMark K T n))}
  set Bad := {x : Fin n → ℝ × ℝ | ∃ j, x j ∈ (polygonRegion K)ᶜ} ∪
    ({x | ∃ j, x j ∈ cornerOverlap K (T / n)} ∪
      (witnessFailure K (fun t : Fin m × Bool => t.1) (winA K) (winB K) n y ∪
        {x | ∃ y ∈ Y, ∀ j, x j ∉ polygonRegion K ∩ ball y (δ / 2)}))
  have hgood : ∀ x ∉ Bad, (x ∈ A ↔ x ∈ B) := by
    intro x hx
    have hxP : ∀ j, x j ∈ polygonRegion K := fun j => by
      by_contra h; exact hx (Or.inl ⟨j, h⟩)
    have hxC : ∀ j, x j ∉ cornerOverlap K (T / n) := fun j h => hx (Or.inr (Or.inl ⟨j, h⟩))
    have hxW' : ∀ t, ∃ j, x j ∈ sideWindow K t.1 (winA K t) (winB K t) (y / n) := fun t => by
      by_contra h; push Not at h; exact hx (Or.inr (Or.inr (Or.inl ⟨t, h⟩)))
    have hxN' : ∀ y ∈ Y, ∃ j, x j ∈ polygonRegion K ∩ ball y (δ / 2) := fun y hy => by
      by_contra h; push Not at h; exact hx (Or.inr (Or.inr (Or.inr ⟨y, hy, h⟩)))
    exact trueEv_iff_evN K hn0 hqR hrR hηπ (by rw [htanη]; exact min_le_left _ _)
      (by rw [htanη]; exact min_le_right _ _) hfit hboxF hline' hstep0 hxP hxC
      (witEv_of_windows K hG hn0 hyT hyM hxP hxC hxW') (hYnet x hxN')
  have hAB : μ A ≤ μ B + μ Bad := by
    refine (measure_mono fun x hx => ?_).trans (measure_union_le B Bad)
    by_cases hb : x ∈ Bad
    · exact Or.inr hb
    · exact Or.inl ((hgood x hb).1 hx)
  have hBA : μ B ≤ μ A + μ Bad := by
    refine (measure_mono fun x hx => ?_).trans (measure_union_le A Bad)
    by_cases hb : x ∈ Bad
    · exact Or.inr hb
    · exact Or.inl ((hgood x hb).2 hx)
  have hBad : (μ Bad).toReal < 3 * e := by
    have hout := outside_null hm hv harea n
    have hwit' : μ (witnessFailure K (fun t : Fin m × Bool => t.1) (winA K) (winB K) n y) <
        ENNReal.ofReal e := by
      rw [← ENNReal.ofReal_toReal (measure_ne_top μ _)]
      exact (ENNReal.ofReal_lt_ofReal_iff he).2 hwit
    have hle : μ Bad ≤ μ {x : Fin n → ℝ × ℝ | ∃ j, x j ∈ (polygonRegion K)ᶜ} +
        (μ {x | ∃ j, x j ∈ cornerOverlap K (T / n)} +
          (μ (witnessFailure K (fun t : Fin m × Bool => t.1) (winA K) (winB K) n y) +
            μ {x | ∃ y ∈ Y, ∀ j, x j ∉ polygonRegion K ∩ ball y (δ / 2)})) :=
      (measure_union_le _ _).trans (add_le_add le_rfl ((measure_union_le _ _).trans
        (add_le_add le_rfl (measure_union_le _ _))))
    have hlt : μ Bad < ENNReal.ofReal e + (ENNReal.ofReal e + ENNReal.ofReal e) := by
      refine lt_of_le_of_lt hle ?_
      rw [hout, zero_add]
      exact ENNReal.add_lt_add hcor (ENNReal.add_lt_add hwit' hnf)
    have h3 : ENNReal.ofReal e + (ENNReal.ofReal e + ENNReal.ofReal e) = ENNReal.ofReal (3 * e) := by
      rw [← ENNReal.ofReal_add he.le he.le, ← ENNReal.ofReal_add he.le (by positivity)]
      ring_nf
    rw [h3] at hlt
    have := (ENNReal.toReal_lt_toReal (measure_ne_top _ _) ENNReal.ofReal_ne_top).2 hlt
    rwa [ENNReal.toReal_ofReal (by positivity)] at this
  have hA1 := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨measure_ne_top _ _, measure_ne_top _ _⟩) hAB
  have hB1 := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨measure_ne_top _ _, measure_ne_top _ _⟩) hBA
  rw [ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)] at hA1 hB1
  have hBF' : |(μ B).toReal - pF| < e := hBF
  have he6 : ε = 6 * e := by simp only [e]; ring
  rw [Real.dist_eq, abs_lt]
  rw [abs_lt] at hBF' hCL
  rw [abs_le] at hFC
  obtain ⟨hB₁, hB₂⟩ := hBF'
  obtain ⟨hC₁, hC₂⟩ := hCL
  obtain ⟨hF₁, hF₂⟩ := hFC
  constructor <;> linarith

/-! ### Corollaries -/

/-- **Theorem 1, model form**: the limit is the probability of the event `E` of the untruncated
limit model. -/
theorem theorem1_model {v : Fin m → ℝ × ℝ} (hm : 3 ≤ m) (hv : ConvexPos v) (harea : area v = 1) :
    let K := sidesOf v hm hv harea
    Tendsto (fun n : ℕ => (Measure.pi fun _ : Fin n => polygonSample v hm hv harea)
        {x | TrueEv K x}) atTop (𝓝 (model K {ω | UFit K ω})) := by
  intro K
  rw [untruncated_prob (goodSides_of_convex hm hv harea)]
  exact theorem1 hm hv harea

/-- **Corollary 2 for random points**: for a counterclockwise triangle of area one with side
lengths `Lᵢ`, the probability tends to `p(L₁², L₂², L₃²)`. -/
theorem theorem1_triangle {w : Fin 3 → ℝ × ℝ} (harea : area w = 1) :
    let hv := convexPos_triangle (w := w) (by rw [harea]; norm_num)
    let K := sidesOf w (le_refl 3) hv harea
    Tendsto (fun n : ℕ => (Measure.pi fun _ : Fin n => polygonSample w (le_refl 3) hv harea)
        {x | TrueEv K x}) atTop
      (𝓝 (ENNReal.ofReal (ptri (len w 0 ^ 2) (len w 1 ^ 2) (len w 2 ^ 2)))) := by
  intro hv K
  have hG := goodSides_of_convex (le_refl 3) hv harea
  have h1 := theorem1 (le_refl 3) hv harea
  have heq := tendsto_nhds_unique (general_optFit_limit hG) (triangle_vertices_optFit_limit harea)
  dsimp only at h1
  rw [heq] at h1
  exact h1

/-- The equilateral triangle of area one, by its vertices. -/
noncomputable def eqVerts : Fin 3 → ℝ × ℝ :=
  ![(0, 0), (eqL, 0), (eqL / 2, eqL * Real.sqrt 3 / 2)]

lemma eqVerts_area : area eqVerts = 1 := by
  simp only [area, Fin.sum_univ_three, eqVerts]
  simp
  have h := eqL_sq
  have h3 := sqrt3_sq
  have hp := sqrt3_pos
  rw [show eqL * (eqL * Real.sqrt 3 / 2) = eqL ^ 2 * Real.sqrt 3 / 2 by ring, h]
  field_simp
  norm_num

lemma eqVerts_len_sq (i : Fin 3) : len eqVerts i ^ 2 = eqL ^ 2 := by
  rw [len_sq]
  have h3 := sqrt3_sq
  fin_cases i <;> simp [edge, eqVerts] <;> ring_nf <;> rw [h3] <;> ring

/-- **The equilateral triangle: `P(E_n) → 13/48`.** For `n` uniform random points in an
equilateral triangle, the probability that some smallest equilateral triangle containing them
(of any orientation) lies inside the original triangle tends to `13/48`. -/
theorem theorem1_equilateral :
    let hv := convexPos_triangle (w := eqVerts) (by rw [eqVerts_area]; norm_num)
    let K := sidesOf eqVerts (le_refl 3) hv eqVerts_area
    Tendsto (fun n : ℕ => (Measure.pi fun _ : Fin n =>
        polygonSample eqVerts (le_refl 3) hv eqVerts_area) {x | TrueEv K x}) atTop
      (𝓝 (ENNReal.ofReal (13 / 48))) := by
  intro hv K
  have h := theorem1_triangle eqVerts_area
  simp only [eqVerts_len_sq] at h
  rwa [ptri_equal (by have := eqL_pos; positivity)] at h

end Enclosing
