import EnclosingCopy.Enclosing.Theorem1Null

/-!
# Theorem 1: a fitting optimum can be taken to fit strictly

`NonDeg` collects the null events of `Theorem1Null` (and `Opp2`, `Tri3`); it holds almost surely
(`nonDeg_ae`). On it, if some optimal copy fits then some optimal copy fits strictly
(`strict_rep`), which is the margin hypothesis of `tangent_enclosing_event_stability`.

For a vertex optimum the optimal face is one point, whose fit slacks are nonzero. For a segment
optimum the face is a chord `c ↦ segCopy v c`; along it every fit slack and every feasibility
slack is affine in `c`, and `local_strict` moves a fitting point to a strictly fitting one unless
two active slopes have opposite signs, an active slope is zero, or an active fit meets a tight
point with nonzero slope.
-/

namespace Enclosing
open MeasureTheory Set Filter Topology Matrix

/-- **One-dimensional lemma.** Affine fit slacks `σ a + c tₐ ≤ 0` and feasibility slacks
`g b + c t'_b ≥ 0` at `c₀`: if active fit slopes are nonzero and of one sign, and every
feasibility slack tight at `c₀` has zero slope when some fit slack is active, then some `c₁` is
feasible with every fit slack strictly negative. -/
lemma local_strict {ι κ : Type*} [Finite ι] [Finite κ] (σ ts : ι → ℝ) (g tg : κ → ℝ) (c₀ : ℝ)
    (hfit : ∀ a, σ a + c₀ * ts a ≤ 0) (hfeas : ∀ b, 0 ≤ g b + c₀ * tg b)
    (h1 : ∀ a, σ a + c₀ * ts a = 0 → ts a ≠ 0)
    (h2 : ∀ a a', σ a + c₀ * ts a = 0 → σ a' + c₀ * ts a' = 0 → 0 ≤ ts a * ts a')
    (h3 : ∀ a b, σ a + c₀ * ts a = 0 → g b + c₀ * tg b = 0 → tg b = 0) :
    ∃ c₁, (∀ a, σ a + c₁ * ts a < 0) ∧ ∀ b, 0 ≤ g b + c₁ * tg b := by
  by_cases hact : ∃ a₀, σ a₀ + c₀ * ts a₀ = 0
  · obtain ⟨a₀, ha₀⟩ := hact
    have hta₀ := h1 a₀ ha₀
    set d := -ts a₀
    have hfa : ∀ a, ∀ᶠ δ in 𝓝[>] (0 : ℝ), σ a + (c₀ + δ * d) * ts a < 0 := by
      intro a
      by_cases ha : σ a + c₀ * ts a = 0
      · filter_upwards [self_mem_nhdsWithin] with δ (hδ : 0 < δ)
        have hpos : 0 < ts a₀ * ts a :=
          lt_of_le_of_ne (h2 a₀ a ha₀ ha) (mul_ne_zero hta₀ (h1 a ha)).symm
        have : σ a + (c₀ + δ * d) * ts a = -(δ * (ts a₀ * ts a)) := by
          simp only [d]; linear_combination ha
        rw [this]; exact neg_neg_of_pos (mul_pos hδ hpos)
      · have hlt : σ a + c₀ * ts a < 0 := lt_of_le_of_ne (hfit a) ha
        have hc : Tendsto (fun δ : ℝ => σ a + (c₀ + δ * d) * ts a) (𝓝[>] 0)
            (𝓝 (σ a + (c₀ + 0 * d) * ts a)) :=
          ((continuous_const.add ((continuous_const.add (continuous_id.mul continuous_const)).mul
            continuous_const)).tendsto 0).mono_left nhdsWithin_le_nhds
        rw [zero_mul, add_zero] at hc
        exact hc.eventually (Iio_mem_nhds hlt)
    have hfb : ∀ b, ∀ᶠ δ in 𝓝[>] (0 : ℝ), 0 ≤ g b + (c₀ + δ * d) * tg b := by
      intro b
      by_cases hb : g b + c₀ * tg b = 0
      · have ht := h3 a₀ b ha₀ hb
        refine Eventually.of_forall fun δ => ?_
        rw [ht]; rw [ht] at hb; linarith
      · have hlt : 0 < g b + c₀ * tg b := lt_of_le_of_ne (hfeas b) (Ne.symm hb)
        have hc : Tendsto (fun δ : ℝ => g b + (c₀ + δ * d) * tg b) (𝓝[>] 0)
            (𝓝 (g b + (c₀ + 0 * d) * tg b)) :=
          ((continuous_const.add ((continuous_const.add (continuous_id.mul continuous_const)).mul
            continuous_const)).tendsto 0).mono_left nhdsWithin_le_nhds
        rw [zero_mul, add_zero] at hc
        exact (hc.eventually (Ioi_mem_nhds hlt)).mono fun δ h => le_of_lt h
    obtain ⟨δ, hδa, hδb⟩ := ((eventually_all.2 hfa).and (eventually_all.2 hfb)).exists
    exact ⟨c₀ + δ * d, hδa, hδb⟩
  · push Not at hact
    exact ⟨c₀, fun a => lt_of_le_of_ne (hfit a) (hact a), hfeas⟩

variable {m : ℕ} (K : Sides m)

/-- The end of side `i` selected by `b`. -/
def endPt (i : Fin m) (b : Bool) : ℝ := if b then K.b i else K.a i

lemma min_endPt (Θ : ℝ) (i : Fin m) :
    ∃ b, min (Θ * K.a i) (Θ * K.b i) = Θ * endPt K i b := by
  rcases min_choice (Θ * K.a i) (Θ * K.b i) with h | h
  · exact ⟨false, by rw [h]; rfl⟩
  · exact ⟨true, by rw [h]; rfl⟩

lemma le_min_iff_endPt (x Θ : ℝ) (i : Fin m) :
    x ≤ min (Θ * K.a i) (Θ * K.b i) ↔ ∀ b, x - Θ * endPt K i b ≤ 0 := by
  rw [le_min_iff]
  constructor
  · rintro ⟨ha, hb⟩ b; cases b <;> simp [endPt] <;> linarith
  · intro h; have ha := h false; have hb := h true; simp [endPt] at ha hb
    exact ⟨by linarith, by linarith⟩

lemma lt_min_iff_endPt (x Θ : ℝ) (i : Fin m) :
    x < min (Θ * K.a i) (Θ * K.b i) ↔ ∀ b, x - Θ * endPt K i b < 0 := by
  rw [lt_min_iff]
  constructor
  · rintro ⟨ha, hb⟩ b; cases b <;> simp [endPt] <;> linarith
  · intro h; have ha := h false; have hb := h true; simp [endPt] at ha hb
    exact ⟨by linarith, by linarith⟩

/-- The linear form whose vanishing says that two kinks of opposite slope meet. -/
noncomputable def kinkPair (k : Fin m) (i : Fin m) (b : Bool) (i' : Fin m) (b' : Bool) :
    Fin 3 → ℝ :=
  (segSlope K k i)⁻¹ • segFitLin K k i (endPt K i b) -
    (segSlope K k i')⁻¹ • segFitLin K k i' (endPt K i' b')

/-- **The non-degeneracy event** of the limit LP. -/
def NonDeg (ω : PoissonPP.Sample (Pt m)) : Prop :=
  ¬ BadP (Opp2 K) ω ∧ ¬ BadP (Tri3 K) ω ∧
  (∀ i b, ¬ ∃ f : Fin 4 ↪ Fin ω.1, (vertexMatrix K (ω.2 ∘ f)).det ≠ 0 ∧
      vertexSlack K i (endPt K i b) (ω.2 ∘ f) = 0) ∧
  (∀ k kb i b, segSlope K k i = 0 → ¬ ∃ f : Fin 3 ↪ Fin ω.1,
      (segMat K k kb (ω.2 ∘ f)).det ≠ 0 ∧
      segLin K k kb (segFitLin K k i (endPt K i b)) (ω.2 ∘ f) = 0) ∧
  (∀ k kb i b i' b', segSlope K k i * segSlope K k i' < 0 → ¬ ∃ f : Fin 3 ↪ Fin ω.1,
      (segMat K k kb (ω.2 ∘ f)).det ≠ 0 ∧ segLin K k kb (kinkPair K k i b i' b') (ω.2 ∘ f) = 0) ∧
  (∀ k kb i b, ¬ ∃ f : Fin 4 ↪ Fin ω.1,
      kinkEndSens K k (ω.2 ∘ f) ≠ 0 ∧ kinkEnd K k kb i (endPt K i b) (ω.2 ∘ f) = 0)

variable {K}

lemma segFitLin_ne (hG : GoodSides K) {k i : Fin m} (e : ℝ) (h0 : segSlope K k i = 0) :
    segFitLin K k i e ≠ 0 := by
  intro h
  have h1 := congrFun h 1
  simp [segFitLin, dot] at h1
  simp [segSlope, dot, tang] at h0
  have hk := hG.unit k
  have hi := hG.unit i
  have : ((K.u i).1 ^ 2 + (K.u i).2 ^ 2) * ((K.u k).1 ^ 2 + (K.u k).2 ^ 2) = 0 := by
    linear_combination ((K.u k).1 * (K.u i).1 + (K.u k).2 * (K.u i).2) * h1 +
      (-(K.u i).1 * (K.u k).2 + (K.u i).2 * (K.u k).1) * h0
  rw [hi, hk] at this; norm_num at this

lemma slope_sq_add (hG : GoodSides K) (k j : Fin m) :
    dot (K.u k) (K.u j) ^ 2 + segSlope K k j ^ 2 = 1 := by
  have hk := hG.unit k
  have hj := hG.unit j
  simp only [segSlope, dot, tang]
  linear_combination ((K.u j).1 ^ 2 + (K.u j).2 ^ 2) * hk + hj

lemma u_decomp (hG : GoodSides K) (k j : Fin m) :
    K.u j = (dot (K.u k) (K.u j) * (K.u k).1 - segSlope K k j * (K.u k).2,
      dot (K.u k) (K.u j) * (K.u k).2 + segSlope K k j * (K.u k).1) := by
  have hk := hG.unit k
  apply Prod.ext <;> simp only [segSlope, dot, tang]
  · linear_combination -(K.u j).1 * hk
  · linear_combination -(K.u j).2 * hk

lemma kinkPair_ne (hG : GoodSides K) {k i i' : Fin m} (b b' : Bool)
    (hneg : segSlope K k i * segSlope K k i' < 0) : kinkPair K k i b i' b' ≠ 0 := by
  intro h
  have hti : segSlope K k i ≠ 0 := by intro h0; rw [h0, zero_mul] at hneg; exact lt_irrefl 0 hneg
  have hti' : segSlope K k i' ≠ 0 := by intro h0; rw [h0, mul_zero] at hneg; exact lt_irrefl 0 hneg
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  simp [kinkPair, segFitLin] at h0 h1
  set t := segSlope K k i with ht
  set t' := segSlope K k i' with ht'
  set α := dot (K.u k) (K.u i) with hα
  set α' := dot (K.u k) (K.u i') with hα'
  have hrel : α * t' = α' * t := by
    field_simp at h1; linarith
  have hai : α ^ 2 + t ^ 2 = 1 := slope_sq_add hG k i
  have hai' : α' ^ 2 + t' ^ 2 = 1 := slope_sq_add hG k i'
  have hsq : t ^ 2 = t' ^ 2 := by
    have e : (α * t') ^ 2 = (α' * t) ^ 2 := by rw [hrel]
    nlinarith [e, hai, hai']
  have htt : t' = -t := by
    have : (t - t') * (t + t') = 0 := by ring_nf; linarith
    rcases mul_eq_zero.mp this with h' | h'
    · have : t = t' := by linarith
      rw [this] at hneg; nlinarith [sq_nonneg t']
    · linarith
  have haa : α' = -α := by
    rw [htt] at hrel
    have : (α' + α) * t = 0 := by linarith
    have := (mul_eq_zero.mp this).resolve_right hti
    linarith
  have hu : K.u i' = -K.u i := by
    rw [u_decomp hG k i', u_decomp hG k i, ← hα', ← hα, ← ht', ← ht, htt, haa]
    apply Prod.ext <;> simp <;> ring
  have hw := hG.width i i' hu
  rw [htt] at h0
  field_simp at h0
  linarith

variable (K) in
lemma segLin_sub_smul (k kb : Fin m) (α β : ℝ) (ℓ ℓ' : Fin 3 → ℝ) (x : Fin 3 → Pt m) :
    segLin K k kb (α • ℓ - β • ℓ') x = α * segLin K k kb ℓ x - β * segLin K k kb ℓ' x := by
  simp only [segLin, sub_dotProduct, smul_dotProduct, smul_eq_mul]

/-- **Non-degeneracy holds almost surely.** -/
theorem nonDeg_ae (hG : GoodSides K) (T : ℝ) : ∀ᵐ ω ∂PoissonPP.law (Λ K T), NonDeg K ω := by
  have hO := measure_eq_zero_iff_ae_notMem.1 (opp2_null K T)
  have hT := measure_eq_zero_iff_ae_notMem.1 (tri3_null K T)
  have hV : ∀ᵐ ω ∂PoissonPP.law (Λ K T), ∀ i b, ¬ ∃ f : Fin 4 ↪ Fin ω.1,
      (vertexMatrix K (ω.2 ∘ f)).det ≠ 0 ∧ vertexSlack K i (endPt K i b) (ω.2 ∘ f) = 0 := by
    rw [ae_all_iff]; intro i; rw [ae_all_iff]; intro b
    exact measure_eq_zero_iff_ae_notMem.1 (vertex_strict_null K hG T i (endPt K i b))
  have hS1 : ∀ᵐ ω ∂PoissonPP.law (Λ K T), ∀ k kb i b, segSlope K k i = 0 → ¬ ∃ f : Fin 3 ↪ Fin ω.1,
      (segMat K k kb (ω.2 ∘ f)).det ≠ 0 ∧
      segLin K k kb (segFitLin K k i (endPt K i b)) (ω.2 ∘ f) = 0 := by
    rw [ae_all_iff]; intro k; rw [ae_all_iff]; intro kb; rw [ae_all_iff]; intro i
    rw [ae_all_iff]; intro b
    by_cases h0 : segSlope K k i = 0
    · filter_upwards [measure_eq_zero_iff_ae_notMem.1
        (segLin_null K k kb T (segFitLin_ne hG (endPt K i b) h0))] with ω hω _
      exact hω
    · exact Eventually.of_forall fun ω h => absurd h h0
  have hS2 : ∀ᵐ ω ∂PoissonPP.law (Λ K T), ∀ k kb i b i' b',
      segSlope K k i * segSlope K k i' < 0 → ¬ ∃ f : Fin 3 ↪ Fin ω.1,
      (segMat K k kb (ω.2 ∘ f)).det ≠ 0 ∧ segLin K k kb (kinkPair K k i b i' b') (ω.2 ∘ f) = 0 := by
    rw [ae_all_iff]; intro k; rw [ae_all_iff]; intro kb; rw [ae_all_iff]; intro i
    rw [ae_all_iff]; intro b; rw [ae_all_iff]; intro i'; rw [ae_all_iff]; intro b'
    by_cases hn : segSlope K k i * segSlope K k i' < 0
    · filter_upwards [measure_eq_zero_iff_ae_notMem.1
        (segLin_null K k kb T (kinkPair_ne hG b b' hn))] with ω hω _
      exact hω
    · exact Eventually.of_forall fun ω h => absurd h hn
  have hS3 : ∀ᵐ ω ∂PoissonPP.law (Λ K T), ∀ k kb i b, ¬ ∃ f : Fin 4 ↪ Fin ω.1,
      kinkEndSens K k (ω.2 ∘ f) ≠ 0 ∧ kinkEnd K k kb i (endPt K i b) (ω.2 ∘ f) = 0 := by
    rw [ae_all_iff]; intro k; rw [ae_all_iff]; intro kb; rw [ae_all_iff]; intro i
    rw [ae_all_iff]; intro b
    exact measure_eq_zero_iff_ae_notMem.1 (kinkEnd_null K k kb T i (endPt K i b))
  filter_upwards [hO, hT, hV, hS1, hS2, hS3] with ω h1 h2 h3 h4 h5 h6
  exact ⟨h1, h2, h3, h4, h5, h6⟩

/-- **A fitting optimal face contains a strictly fitting copy**, on the non-degeneracy event. -/
theorem strict_rep (hG : GoodSides K) {n : ℕ} (y : Fin n → Pt m) (hnd : NonDeg K ⟨n, y⟩)
    (zs : Copy) (hopt : ∀ z', Feasible K (PoissonPP.config y) z' → zs.1 ≤ z'.1)
    (hfit : ∃ z, Feasible K (PoissonPP.config y) z ∧ z.1 = zs.1 ∧ Fits K z) :
    ∃ z, Feasible K (PoissonPP.config y) z ∧ z.1 = zs.1 ∧
      ∀ i, Hs K z i < min (z.2.2 * K.a i) (z.2.2 * K.b i) := by
  obtain ⟨z, hzf, hz1, hzF⟩ := hfit
  have hzopt : ∀ z', Feasible K (PoissonPP.config y) z' → z.1 ≤ z'.1 := fun z' h =>
    hz1 ▸ hopt z' h
  obtain ⟨hnO, hnT, hnV, hnS1, hnS2, hnS3⟩ := hnd
  rcases optimum_structure K hG y z hzf hzopt with ⟨f, hA, -, hzv⟩ | ⟨k, kb, hu, g, hg, hzs⟩ |
      h | h
  · -- vertex: the copy itself fits strictly
    refine ⟨z, hzf, hz1, fun i => (lt_min_iff_endPt K _ _ i).2 fun b => ?_⟩
    have hle := (le_min_iff_endPt K _ _ i).1 (hzF i) b
    refine lt_of_le_of_ne hle fun heq => hnV i b ⟨f, hA, ?_⟩
    rw [vertexSlack, ← hzv]; exact heq
  · -- segment: move along the chord
    have hP := hG.parPair hu
    set v := segVec K k kb (y ∘ g)
    set c₀ := dot z.2.1 (tang K k)
    have hM := segMat_det_ne hP hg
    let σ : Fin m × Bool → ℝ := fun a => segFitLin K k a.1 (endPt K a.1 a.2) ⬝ᵥ v
    let ts : Fin m × Bool → ℝ := fun a => segSlope K k a.1
    let gg : Fin n → ℝ := fun t => segFitLin K k (y t).1 (y t).2.1 ⬝ᵥ v + (y t).2.2
    let tg : Fin n → ℝ := fun t => segSlope K k (y t).1
    have hfitc : ∀ c a, (Hs K (segCopy K k v c) a.1 -
        (segCopy K k v c).2.2 * endPt K a.1 a.2) = σ a + c * ts a := fun c a =>
      Hs_segCopy K k v c a.1 _
    have hgc : ∀ c t, gx K (segCopy K k v c) (y t) = gg t + c * tg t := by
      intro c t; rw [gx_segCopy_lin]; simp only [gg, tg]; ring
    have hk0 : segSlope K k k = 0 := by simp [segSlope, dot, tang]; ring
    have hkb0 : segSlope K k kb = 0 := by
      simp only [segSlope]; rw [hu]; simp [dot, tang]; ring
    have hslope0 : ∀ r, tg (g r) = 0 := by
      intro r
      match r with
      | 0 => show segSlope K k (y (g 0)).1 = 0; rw [show (y (g 0)).1 = k from hg.1]; exact hk0
      | 1 => show segSlope K k (y (g 1)).1 = 0; rw [show (y (g 1)).1 = k from hg.2.1]; exact hk0
      | 2 => show segSlope K k (y (g 2)).1 = 0; rw [show (y (g 2)).1 = kb from hg.2.2.1]
             exact hkb0
    obtain ⟨c₁, hc₁a, hc₁b⟩ := local_strict σ ts gg tg c₀
      (fun a => by rw [← hfitc, ← hzs]; exact (le_min_iff_endPt K _ _ a.1).1 (hzF a.1) a.2)
      (fun t => by rw [← hgc, ← hzs]; exact (feasible_config_iff K y z).1 hzf t)
      (fun a ha h0 => hnS1 k kb a.1 a.2 h0 ⟨g, hM, by
        have h0' : segSlope K k a.1 = 0 := h0
        simp only [σ, ts] at ha; rw [h0', mul_zero, add_zero] at ha; exact ha⟩)
      (fun a a' ha ha' => by
        by_contra hneg
        push Not at hneg
        refine hnS2 k kb a.1 a.2 a'.1 a'.2 hneg ⟨g, hM, ?_⟩
        rw [kinkPair, segLin_sub_smul]
        have ht : ts a ≠ 0 := by intro h0; rw [h0, zero_mul] at hneg; exact lt_irrefl 0 hneg
        have ht' : ts a' ≠ 0 := by intro h0; rw [h0, mul_zero] at hneg; exact lt_irrefl 0 hneg
        have e1 : segLin K k kb (segFitLin K k a.1 (endPt K a.1 a.2)) (y ∘ g) = -(c₀ * ts a) := by
          change σ a = _; linarith
        have e2 : segLin K k kb (segFitLin K k a'.1 (endPt K a'.1 a'.2)) (y ∘ g) =
            -(c₀ * ts a') := by
          change σ a' = _; linarith
        rw [e1, e2]
        have ht1 : ts a = segSlope K k a.1 := rfl
        have ht2 : ts a' = segSlope K k a'.1 := rfl
        rw [ht1] at ht ⊢; rw [ht2] at ht' ⊢
        field_simp
        try ring)
      (fun a t ha ht => by
        by_contra htg
        have hnot : t ∉ Set.range g := by
          rintro ⟨r, rfl⟩; exact htg (hslope0 r)
        have hta : ts a ≠ 0 := by
          intro h0
          refine hnS1 k kb a.1 a.2 h0 ⟨g, hM, ?_⟩
          have h0' : segSlope K k a.1 = 0 := h0
          simp only [σ, ts] at ha; rw [h0', mul_zero, add_zero] at ha; exact ha
        have hc3 : (y ∘ appendEmb3 g t hnot) ∘ Fin.castSucc = y ∘ g := by
          funext r
          show y (Fin.lastCases t g (Fin.castSucc r)) = y (g r)
          rw [Fin.lastCases_castSucc]
        have h33 : (y ∘ appendEmb3 g t hnot) 3 = y t := by
          show y (Fin.lastCases t g (Fin.last 3)) = y t
          rw [Fin.lastCases_last]
        have htg' : segSlope K k (y t).1 ≠ 0 := htg
        have hta' : segSlope K k a.1 ≠ 0 := hta
        refine hnS3 k kb a.1 a.2 ⟨appendEmb3 g t hnot, ?_, ?_⟩
        · simp only [kinkEndSens, h33]; exact inv_ne_zero htg'
        · rw [kinkEnd, hc3, h33]
          have e1 : segFitLin K k (y t).1 (y t).2.1 ⬝ᵥ v + (y t).2.2 =
              -(c₀ * segSlope K k (y t).1) := by
            change gg t = _; linarith
          have e2 : segFitLin K k a.1 (endPt K a.1 a.2) ⬝ᵥ v = -(c₀ * segSlope K k a.1) := by
            change σ a = _; linarith
          rw [e1, e2, neg_neg, neg_mul, mul_assoc, mul_assoc, mul_inv_cancel₀ htg',
            mul_inv_cancel₀ hta']
          ring)
    refine ⟨segCopy K k v c₁, (feasible_config_iff K y _).2 fun t => by rw [hgc]; exact hc₁b t,
      ?_, fun i => (lt_min_iff_endPt K _ _ i).2 fun b => by
        have h := hfitc c₁ (i, b); dsimp only at h; rw [h]; exact hc₁a (i, b)⟩
    rw [← hz1, hzs]; rfl
  · exact absurd h hnO
  · exact absurd h hnT

end Enclosing
