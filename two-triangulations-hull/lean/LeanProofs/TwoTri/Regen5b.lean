import LeanProofs.TwoTri.Regen5

/-!
# Lemma 5: the case `m ≥ 4`, and the ingredients of Step 1
-/

set_option linter.unusedSectionVars false

namespace TwoTri

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- **Case `m ≥ 4`.** A face `T` of `B` meeting the open side `uv` of `α`, different from `β` and
without `u, v` as vertices, gives the good pair `(uvp, T)`. -/
theorem good_of_chain {P : Finset (K × K)} (hP : GenPos P) {A B A' B' : Finset (Sym2 (K × K))}
    {u v o p b₁ b₂ b₃ t₁ t₂ t₃ : K × K} (hα : Face P A u v o) (hpα : InTri u v o p)
    (hAA : A ⊆ A') (hpu : s(p, u) ∈ A') (hpv : s(p, v) ∈ A')
    (hβ : Face P B b₁ b₂ b₃) (hpβ : InTri b₁ b₂ b₃ p) (hBB : B ⊆ B') (hBnc : NonCross B)
    (hT : Face P B t₁ t₂ t₃) (hTne : ∃ w, VertexOf t₁ t₂ t₃ w ∧ ¬ VertexOf b₁ b₂ b₃ w)
    (hTuv : ∀ w, VertexOf t₁ t₂ t₃ w → w ≠ u ∧ w ≠ v) (hm : MeetsSide u v t₁ t₂ t₃) :
    GoodPair (insert p P) A' B' := by
  have hpP := hα.not_mem hpα
  have fα := hα.piece hpα hAA hpu hpv
  have fT : Face (insert p P) B' t₁ t₂ t₃ := by
    refine hT.mono hBB fun hin => ?_
    obtain ⟨c1, c2, c3⟩ := faces_vertices hP hBnc hβ hT hpβ hin
    obtain ⟨w, hw, hnw⟩ := hTne
    rcases hw with rfl | rfl | rfl <;> [exact hnw c1; exact hnw c2; exact hnw c3]
  obtain ⟨ht1, ht2, ht3, -⟩ := id hT
  obtain ⟨s, hs0, hs1, hin⟩ := hm
  have hD := hpα.1
  set m := lerp u v s
  obtain ⟨ε, hε, hc, -⟩ := exists_small (Finset.univ : Finset (Fin 4)) (∅ : Finset Unit)
    ![orient t₁ t₂ m, orient t₂ t₃ m, orient t₃ t₁ m, 1]
    ![orient t₁ t₂ p - orient t₁ t₂ m, orient t₂ t₃ p - orient t₂ t₃ m,
      orient t₃ t₁ p - orient t₃ t₁ m, -1] (fun _ => (1 : K)) (fun _ => 0)
    (by intro i _; fin_cases i; exacts [hin.1, hin.2.1, hin.2.2, one_pos]) (by simp)
  have c0 := hc 0 (by simp); have c1 := hc 1 (by simp)
  have c2 := hc 2 (by simp); have c3 := hc 3 (by simp)
  simp at c0 c1 c2 c3
  have e2 : orient v p m = (1 - s) * orient u v p := by
    simp only [m]; unfold orient lerp; ring
  have e3 : orient p u m = s * orient u v p := by
    simp only [m]; unfold orient lerp; ring
  refine ⟨u, v, p, t₁, t₂, t₃, fα, fT, ?_, lerp m p ε, ?_, ?_⟩
  · intro w hw hwT
    rcases hw with rfl | rfl | rfl
    · exact (hTuv w hwT).1 rfl
    · exact (hTuv w hwT).2 rfl
    · rcases hwT with rfl | rfl | rfl <;> contradiction
  · refine ⟨?_, ?_, ?_⟩ <;> rw [orient_lerp]
    · rw [orient_lerp_self]; simp; exact mul_pos hε hD
    · rw [e2, orient_self23]; nlinarith [mul_pos (sub_pos.mpr hs1) hD]
    · rw [e3, orient_self13]; nlinarith [mul_pos hs0 hD]
  · refine ⟨?_, ?_, ?_⟩ <;> rw [orient_lerp] <;> linarith

/-- Leaving `β` from a point of the open segment `xy` towards `x`. -/
lemma exit_dir {P : Finset (K × K)} (hP : GenPos P) {T : Finset (Sym2 (K × K))}
    {x y b₁ b₂ b₃ : K × K} (hx : x ∈ P) (hy : y ∈ P) (hxy : x ≠ y) (hβ : Face P T b₁ b₂ b₃)
    (hxn : ¬ VertexOf b₁ b₂ b₃ x) {s₀ : K} (hs0 : 0 < s₀) (hs1 : s₀ < 1)
    (hm : InTri b₁ b₂ b₃ (lerp x y s₀)) :
    ∃ u v o, Rot b₁ b₂ b₃ u v o ∧ ∃ s₁ σ : K, 0 < s₁ ∧ s₁ < s₀ ∧ 0 < σ ∧ σ < 1 ∧
      lerp x y s₁ = lerp u v σ ∧ orient u v x < 0 ∧ 0 < orient u v y := by
  obtain ⟨hb1, hb2, hb3, hD, -, -, -, he⟩ := id hβ
  obtain ⟨h12, h23, h31⟩ := hβ.ne
  unfold VertexOf at hxn; push Not at hxn
  have hout : orient b₁ b₂ x < 0 ∨ orient b₂ b₃ x < 0 ∨ orient b₃ b₁ x < 0 := by
    have n1 := hP b₁ hb1 b₂ hb2 x hx h12 (Ne.symm hxn.1) (Ne.symm hxn.2.1)
    have n2 := hP b₂ hb2 b₃ hb3 x hx h23 (Ne.symm hxn.2.1) (Ne.symm hxn.2.2)
    have n3 := hP b₃ hb3 b₁ hb1 x hx h31 (Ne.symm hxn.2.2) (Ne.symm hxn.1)
    by_contra hc; push Not at hc
    exact he x hx ⟨lt_of_le_of_ne hc.1 (Ne.symm n1), lt_of_le_of_ne hc.2.1 (Ne.symm n2),
      lt_of_le_of_ne hc.2.2 (Ne.symm n3)⟩
  obtain ⟨t, ht0, ht1, hcase⟩ := exit' hm hout
  have hpt : lerp (lerp x y s₀) x t = lerp x y (s₀ - s₀ * t) := lerp_lerp_start _ _ _ _
  have hs := (lerp_sub_mem hs0 hs1 ht0 ht1).1
  rcases hcase with hv | ⟨u, v, o, hrot, h0, hp1, hp2⟩
  · exfalso
    have novert : ∀ b ∈ P, b ≠ x → lerp (lerp x y s₀) x t = b → False := by
      intro b hb hbx e
      have : orient x y b = 0 := by rw [← e, hpt, orient_lerp_self]
      rcases hP.on_line hx hy hb hxy this with h | h
      · exact hbx h
      · have : lerp x y (s₀ - s₀ * t) = lerp x y 1 := by rw [← hpt, e, h, lerp_one]
        have := lerp_inj hxy this; linarith
    rcases hv with hv | hv | hv
    · exact novert b₁ hb1 (Ne.symm hxn.1) hv
    · exact novert b₂ hb2 (Ne.symm hxn.2.1) hv
    · exact novert b₃ hb3 (Ne.symm hxn.2.2) hv
  · obtain ⟨σ, hσ0, hσ1, hmσ⟩ := on_side h0 hp1 hp2
    have hmuv : 0 < orient u v (lerp x y s₀) := (hrot.inTri hm).1
    have E : (1 - t) * orient u v (lerp x y s₀) + t * orient u v x = 0 := by
      rw [← orient_lerp]; exact h0
    have hxneg : orient u v x < 0 := by nlinarith
    have hypos : 0 < orient u v y := by
      rw [orient_lerp] at hmuv; nlinarith
    exact ⟨u, v, o, hrot, s₀ - s₀ * t, σ, hs.1, by nlinarith, hσ0, hσ1, hpt ▸ hmσ, hxneg, hypos⟩

/-- "No face of `T` other than `abc` meets the open segment `uv` without having `u` or `v` as a
vertex": the hypothesis of the remaining case of Lemma 5. -/
def NoChain (P : Finset (K × K)) (T : Finset (Sym2 (K × K))) (u v a b c : K × K) : Prop :=
  ∀ t₁ t₂ t₃, Face P T t₁ t₂ t₃ → MeetsSide u v t₁ t₂ t₃ →
    (∃ w, VertexOf t₁ t₂ t₃ w ∧ ¬ VertexOf a b c w) → VertexOf t₁ t₂ t₃ u ∨ VertexOf t₁ t₂ t₃ v

/-- Moving from a point of the open segment `uv` towards an endpoint stays in the open segment. -/
lemma toward_end {u v c : K × K} {σ ε : K} (hσ0 : 0 < σ) (hσ1 : σ < 1) (hε0 : 0 < ε)
    (hε1 : ε < 1) (hc : c = lerp u v σ) (q : K × K) (hq : q = u ∨ q = v) :
    ∃ σ' : K, 0 < σ' ∧ σ' < 1 ∧ lerp c q ε = lerp u v σ' := by
  have h := lerp_sub_mem hσ0 hσ1 hε0 hε1
  rcases hq with rfl | rfl
  · exact ⟨_, h.1.1, h.1.2, by rw [hc, lerp_lerp_start]⟩
  · exact ⟨_, h.2.1, h.2.2, by rw [hc, lerp_lerp]⟩

/-- Step 1, first part: the face of `B` beyond the side of `β` crossed towards `x` has third
vertex `x`. -/
lemma beyond_is_target {P : Finset (K × K)} (hP : GenPos P) {B : Finset (Sym2 (K × K))}
    (hB : IsTri P B) {x y b₁ b₂ b₃ u v o : K × K} (hβ : Face P B b₁ b₂ b₃) (hx : x ∈ P)
    (hy : y ∈ P) (hxβ : ¬ VertexOf b₁ b₂ b₃ x) (hyβ : ¬ VertexOf b₁ b₂ b₃ y)
    (hrot : Rot b₁ b₂ b₃ u v o) {s₁ σ : K} (hs0 : 0 < s₁) (hs1 : s₁ < 1) (hσ0 : 0 < σ)
    (hσ1 : σ < 1) (hc : lerp x y s₁ = lerp u v σ) (hxneg : orient u v x < 0)
    (hypos : 0 < orient u v y) (NA : NoChain P B x y b₁ b₂ b₃) : Face P B v u x := by
  have hβ' := hrot.face hβ
  obtain ⟨hu, hv, ho, hD, huv, -, -, -⟩ := id hβ'
  obtain ⟨hne1, -, -⟩ := hβ'.ne
  obtain ⟨t, ht, hF⟩ := side_face hP hB hv hu (by rw [Sym2.eq_swap]; exact huv)
    ⟨x, hx, by rw [orient_swap12]; linarith⟩
  have hFD := hF.2.2.2.1
  -- `T₁ = v u t` meets the open segment `xy`
  have hc' : lerp x y s₁ = lerp v u (1 - σ) := by rw [hc, ← lerp_symm]
  obtain ⟨ε, hε0, hε1, hin⟩ := near_side hFD (σ := 1 - σ) (by linarith) (by linarith)
    (q := x) (by rw [orient_swap12]; linarith)
  rw [← hc', lerp_lerp_start] at hin
  have hmeet : MeetsSide x y v u t := ⟨_, (lerp_sub_mem hs0 hs1 hε0 hε1).1.1,
    (lerp_sub_mem hs0 hs1 hε0 hε1).1.2, hin⟩
  -- `T₁ ≠ β`
  have hto : t ≠ o := by
    rintro rfl
    have := hrot.orient; rw [orient_swap12] at hFD; linarith [hβ.2.2.2.1]
  obtain ⟨-, hut, htv⟩ := hF.ne
  have hnew : ∃ w, VertexOf v u t w ∧ ¬ VertexOf b₁ b₂ b₃ w := by
    refine ⟨t, Or.inr (Or.inr rfl), fun h => ?_⟩
    rcases hrot.vertexOf.mpr h with h | h | h
    exacts [hut h.symm, htv h, hto h]
  have huxy : u ≠ x ∧ u ≠ y := ⟨fun h => hxβ (hrot.vertexOf.mp (Or.inl h.symm)),
    fun h => hyβ (hrot.vertexOf.mp (Or.inl h.symm))⟩
  have hvxy : v ≠ x ∧ v ≠ y := ⟨fun h => hxβ (hrot.vertexOf.mp (Or.inr (Or.inl h.symm))),
    fun h => hyβ (hrot.vertexOf.mp (Or.inr (Or.inl h.symm)))⟩
  rcases NA v u t hF hmeet hnew with h | h
  · rcases h with h | h | h
    · exact absurd h.symm hvxy.1
    · exact absurd h.symm huxy.1
    · rw [h]; exact hF
  · exfalso
    rcases h with h | h | h
    · exact hvxy.2 h.symm
    · exact huxy.2 h.symm
    · rw [← h, orient_swap12] at hFD; linarith

/-- Step 1, second part: the face `D = y x d` of `A` beyond `xy` has `d` an endpoint of every side
of `β` that crosses `xy`. -/
lemma d_vertex {P : Finset (K × K)} (hP : GenPos P) {A : Finset (Sym2 (K × K))}
    {x y z d u v : K × K} (hα : Face P A x y z) (hD : Face P A y x d) (hu : u ∈ P) (hv : v ∈ P)
    (huv : u ≠ v) (hux : u ≠ x) (huy : u ≠ y) (hvx : v ≠ x) (hvy : v ≠ y)
    {s₁ σ : K} (hs0 : 0 < s₁) (hs1 : s₁ < 1) (hσ0 : 0 < σ) (hσ1 : σ < 1)
    (hc : lerp x y s₁ = lerp u v σ) (NB : MeetsSide u v x y z → NoChain P A u v x y z) :
    d = u ∨ d = v := by
  obtain ⟨hx, hy, hz, hαD, -, -, -, -⟩ := id hα
  obtain ⟨hxy, -, -⟩ := hα.ne
  have hx' := cross_of_common hP hx hy hu hv hxy huv
    (fun e => by rcases Sym2.eq_iff.mp e with ⟨h, -⟩ | ⟨h, -⟩ <;> [exact hux h.symm; exact hvx h.symm])
    hs0 hs1 hσ0.le hσ1.le hc
  have hsep := hx'.1
  -- an endpoint `q` of `uv` on the side of `α`, the other `q'` on the side of `D`
  have pick : ∃ q q', (q = u ∨ q = v) ∧ (q' = u ∨ q' = v) ∧ 0 < orient x y q ∧
      orient x y q' < 0 := by
    rcases lt_or_gt_of_ne (show orient x y u ≠ 0 from fun h0 => by
      rw [h0, zero_mul] at hsep; exact lt_irrefl _ hsep) with h | h
    · exact ⟨v, u, Or.inr rfl, Or.inl rfl, by nlinarith, h⟩
    · exact ⟨u, v, Or.inl rfl, Or.inr rfl, h, by nlinarith⟩
  obtain ⟨q, q', hq, hq', hqp, hq'n⟩ := pick
  have hmα : MeetsSide u v x y z := by
    obtain ⟨ε, hε0, hε1, hin⟩ := near_side hαD hs0 hs1 hqp
    obtain ⟨σ', h0, h1, he⟩ := toward_end hσ0 hσ1 hε0 hε1 hc q hq
    exact ⟨σ', h0, h1, he ▸ hin⟩
  have hDD := hD.2.2.2.1
  have hmD : MeetsSide u v y x d := by
    have hc' : lerp y x (1 - s₁) = lerp u v σ := by rw [lerp_symm]; exact hc
    obtain ⟨ε, hε0, hε1, hin⟩ := near_side hDD (σ := 1 - s₁) (by linarith) (by linarith)
      (q := q') (by rw [orient_swap12]; linarith)
    obtain ⟨σ', h0, h1, he⟩ := toward_end hσ0 hσ1 hε0 hε1 hc' q' hq'
    exact ⟨σ', h0, h1, he ▸ hin⟩
  obtain ⟨-, hxd, hdy⟩ := hD.ne
  have hdz : d ≠ z := by
    rintro rfl; rw [orient_swap12] at hDD; linarith
  rcases NB hmα y x d hD hmD ⟨d, Or.inr (Or.inr rfl), by
      rintro (h | h | h)
      exacts [hxd.symm h, hdy h, hdz h]⟩ with h | h
  · rcases h with h | h | h
    exacts [absurd h huy, absurd h hux, Or.inl h.symm]
  · rcases h with h | h | h
    exacts [absurd h hvy, absurd h hvx, Or.inr h.symm]

/-- The open segments `xy` and `de` meet. -/
def Crosses (x y d e : K × K) : Prop :=
  ∃ s σ : K, 0 < s ∧ s < 1 ∧ 0 < σ ∧ σ < 1 ∧ lerp x y s = lerp d e σ

lemma meetsSide_swap {u v a b c : K × K} (h : MeetsSide u v a b c) : MeetsSide v u a b c := by
  obtain ⟨s, h0, h1, h⟩ := h
  exact ⟨1 - s, by linarith, by linarith, by rw [lerp_symm]; exact h⟩

lemma NoChain.swap {P : Finset (K × K)} {T : Finset (Sym2 (K × K))} {u v a b c : K × K}
    (h : NoChain P T u v a b c) : NoChain P T v u a b c := by
  intro t₁ t₂ t₃ hf hm hn
  exact (h t₁ t₂ t₃ hf (meetsSide_swap hm) hn).symm

/-- **Step 1.** In the remaining case, a side `xy` of `α` meeting the interior of `β` crosses the
two sides of `β` at a vertex `d`, and `xd`, `yd` are hull edges; `y x d` is the face of `A` beyond
`xy`. -/
theorem step1 {P : Finset (K × K)} (hP : GenPos P) {A B : Finset (Sym2 (K × K))}
    (hA : IsTri P A) (hB : IsTri P B) (hAB : A ∩ B = hullEdges P) {x y z b₁ b₂ b₃ : K × K}
    (hα : Face P A x y z) (hβ : Face P B b₁ b₂ b₃)
    (hd : ∀ w, VertexOf x y z w → ¬ VertexOf b₁ b₂ b₃ w) (hm : MeetsSide x y b₁ b₂ b₃)
    (NA : NoChain P B x y b₁ b₂ b₃)
    (NB : ∀ u v o, Rot b₁ b₂ b₃ u v o → MeetsSide u v x y z → NoChain P A u v x y z) :
    ∃ d e f, VertexOf b₁ b₂ b₃ d ∧ VertexOf b₁ b₂ b₃ e ∧ VertexOf b₁ b₂ b₃ f ∧ d ≠ e ∧ d ≠ f ∧
      e ≠ f ∧ Face P A y x d ∧ s(x, d) ∈ hullEdges P ∧ s(y, d) ∈ hullEdges P ∧
      Crosses x y d e ∧ Crosses x y d f := by
  obtain ⟨s₀, hs0, hs1, hm0⟩ := hm
  obtain ⟨hx, hy, hz, hαD, hxyA, -, -, -⟩ := id hα
  obtain ⟨hxy, -, -⟩ := hα.ne
  have hxβ : ¬ VertexOf b₁ b₂ b₃ x := hd x (Or.inl rfl)
  have hyβ : ¬ VertexOf b₁ b₂ b₃ y := hd y (Or.inr (Or.inl rfl))
  have notxy : ∀ w, VertexOf b₁ b₂ b₃ w → w ≠ x ∧ w ≠ y := fun w hw =>
    ⟨fun h => hxβ (h ▸ hw), fun h => hyβ (h ▸ hw)⟩
  -- the two exits
  obtain ⟨u₁, v₁, o₁, r₁, s₁, σ₁, hs₁0, hs₁s, hσ₁0, hσ₁1, hc₁, hx₁, hy₁⟩ :=
    exit_dir hP hx hy hxy hβ hxβ hs0 hs1 hm0
  obtain ⟨u₂, v₂, o₂, r₂, s₂, σ₂, hs₂0, hs₂s, hσ₂0, hσ₂1, hc₂, hy₂, hx₂⟩ :=
    exit_dir hP hy hx (Ne.symm hxy) hβ hyβ (s₀ := 1 - s₀) (by linarith) (by linarith)
      (by rw [lerp_symm]; exact hm0)
  have hc₂' : lerp x y (1 - s₂) = lerp u₂ v₂ σ₂ := by rw [← lerp_symm, sub_sub_cancel]; exact hc₂
  have hβ₁ := r₁.face hβ
  have hβ₂ := r₂.face hβ
  have hu₁ := hβ₁.1; have hv₁ := hβ₁.2.1; have hu₂ := hβ₂.1; have hv₂ := hβ₂.2.1
  obtain ⟨huv₁, -, -⟩ := hβ₁.ne
  obtain ⟨huv₂, -, -⟩ := hβ₂.ne
  have vu₁ := r₁.vertexOf.mp (Or.inl rfl : VertexOf u₁ v₁ o₁ u₁)
  have vv₁ := r₁.vertexOf.mp (Or.inr (Or.inl rfl) : VertexOf u₁ v₁ o₁ v₁)
  have vu₂ := r₂.vertexOf.mp (Or.inl rfl : VertexOf u₂ v₂ o₂ u₂)
  have vv₂ := r₂.vertexOf.mp (Or.inr (Or.inl rfl) : VertexOf u₂ v₂ o₂ v₂)
  -- the faces of `B` beyond the two sides
  have T₁ := beyond_is_target hP hB hβ hx hy hxβ hyβ r₁ hs₁0 (by linarith) hσ₁0 hσ₁1 hc₁ hx₁ hy₁ NA
  have T₃ := beyond_is_target hP hB hβ hy hx hyβ hxβ r₂ hs₂0 (by linarith) hσ₂0 hσ₂1 hc₂ hy₂ hx₂
    NA.swap
  -- the face of `A` beyond `xy`
  have hX := cross_of_common hP hx hy hu₁ hv₁ hxy huv₁
    (fun e => by rcases Sym2.eq_iff.mp e with ⟨h, -⟩ | ⟨h, -⟩ <;>
      [exact (notxy _ vu₁).1 h.symm; exact (notxy _ vv₁).1 h.symm])
    hs₁0 (by linarith) hσ₁0.le hσ₁1.le hc₁
  obtain ⟨d, hdP, hD⟩ := side_face hP hA hy hx (by rw [Sym2.eq_swap]; exact hxyA) (by
    have hsep := hX.1
    rcases lt_or_gt_of_ne (show orient x y u₁ ≠ 0 from fun h0 => by
      rw [h0, zero_mul] at hsep; exact lt_irrefl _ hsep) with h | h
    · exact ⟨u₁, hu₁, by rw [orient_swap12]; linarith⟩
    · exact ⟨v₁, hv₁, by rw [orient_swap12]; nlinarith⟩)
  have hd₁ := d_vertex hP hα hD hu₁ hv₁ huv₁ (notxy _ vu₁).1 (notxy _ vu₁).2 (notxy _ vv₁).1
    (notxy _ vv₁).2 hs₁0 (by linarith) hσ₁0 hσ₁1 hc₁ (NB u₁ v₁ o₁ r₁)
  have hd₂ := d_vertex hP hα hD hu₂ hv₂ huv₂ (notxy _ vu₂).1 (notxy _ vu₂).2 (notxy _ vv₂).1
    (notxy _ vv₂).2 (by linarith) (by linarith) hσ₂0 hσ₂1 hc₂' (NB u₂ v₂ o₂ r₂)
  -- the other endpoints
  have other : ∀ u v : K × K, ∀ s σ : K, 0 < s → s < 1 → 0 < σ → σ < 1 →
      lerp x y s = lerp u v σ → u ≠ v → (d = u ∨ d = v) →
      ∃ e, (e = u ∨ e = v) ∧ d ≠ e ∧ ∃ σ', 0 < σ' ∧ σ' < 1 ∧ lerp x y s = lerp d e σ' := by
    intro u v s σ h0 h1 h2 h3 hc huv hd'
    rcases hd' with rfl | rfl
    · exact ⟨v, Or.inr rfl, huv, σ, h2, h3, hc⟩
    · exact ⟨u, Or.inl rfl, Ne.symm huv, 1 - σ, by linarith, by linarith, by
        rw [hc, ← lerp_symm]⟩
  obtain ⟨e, he, hde, σe, hσe0, hσe1, hce⟩ :=
    other u₁ v₁ s₁ σ₁ hs₁0 (by linarith) hσ₁0 hσ₁1 hc₁ huv₁ hd₁
  obtain ⟨f, hf, hdf, σf, hσf0, hσf1, hcf⟩ :=
    other u₂ v₂ (1 - s₂) σ₂ (by linarith) (by linarith) hσ₂0 hσ₂1 hc₂' huv₂ hd₂
  have hdβ : VertexOf b₁ b₂ b₃ d := by rcases hd₁ with rfl | rfl <;> assumption
  have heβ : VertexOf b₁ b₂ b₃ e := by rcases he with rfl | rfl <;> assumption
  have hfβ : VertexOf b₁ b₂ b₃ f := by rcases hf with rfl | rfl <;> assumption
  -- `e ≠ f`: otherwise the line `de` would meet `xy` twice
  have hef : e ≠ f := by
    rintro rfl
    have E1 : (1 - s₁) * orient d e x + s₁ * orient d e y = 0 := by
      rw [← orient_lerp, hce, orient_lerp_self]
    have E2 : (1 - (1 - s₂)) * orient d e x + (1 - s₂) * orient d e y = 0 := by
      rw [← orient_lerp, hcf, orient_lerp_self]
    have hX0 : orient d e x = 0 := by
      have h12 : (1 - s₂ - s₁) * (orient d e x - orient d e y) = 0 := by linarith
      rcases mul_eq_zero.mp h12 with h | h
      · exfalso; linarith
      · nlinarith
    have hdP' : d ∈ P := hdP
    have heP : e ∈ P := by rcases he with rfl | rfl <;> assumption
    rcases hP.on_line hdP' heP hx hde hX0 with h | h
    · exact (notxy _ hdβ).1 h.symm
    · exact (notxy _ heβ).1 h.symm
  -- hull edges
  have hxdB : s(x, d) ∈ B := by
    obtain ⟨-, -, -, -, -, h2, h3, -⟩ := T₁
    rcases hd₁ with rfl | rfl
    · rw [Sym2.eq_swap]; exact h2
    · exact h3
  have hydB : s(y, d) ∈ B := by
    obtain ⟨-, -, -, -, -, h2, h3, -⟩ := T₃
    rcases hd₂ with rfl | rfl
    · rw [Sym2.eq_swap]; exact h2
    · exact h3
  have hxdA : s(x, d) ∈ A := hD.2.2.2.2.2.1
  have hydA : s(y, d) ∈ A := by rw [Sym2.eq_swap]; exact hD.2.2.2.2.2.2.1
  refine ⟨d, e, f, hdβ, heβ, hfβ, hde, hdf, hef, hD, ?_, ?_, ⟨s₁, σe, hs₁0, by linarith, hσe0,
    hσe1, hce⟩, ⟨1 - s₂, σf, by linarith, by linarith, hσf0, hσf1, hcf⟩⟩
  · rw [← hAB]; exact Finset.mem_inter.mpr ⟨hxdA, hxdB⟩
  · rw [← hAB]; exact Finset.mem_inter.mpr ⟨hydA, hydB⟩

end TwoTri
