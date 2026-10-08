import LeanProofs.TwoTri.Regen5c

/-!
# Lemma 5 (Regeneration)

Let `|P| ≥ 7`, let `A` and `B` be hull-disjoint triangulations of `P` with a good pair
`(α, β)`, and let `A'`, `B'` be obtained by inserting a generic point `p ∈ int α ∩ int β` as in
Lemma 4. Then `A'` and `B'` have a good pair.
-/

set_option linter.unusedSectionVars false

namespace TwoTri

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- **Property (a).** No vertex of `β` lies in the closed face `α`: it is not strictly inside, and
by general position it is on no side line of `α`. -/
theorem prop_a {P : Finset (K × K)} (hP : GenPos P) {T T' : Finset (Sym2 (K × K))}
    {x y z b₁ b₂ b₃ w : K × K} (hα : Face P T x y z) (hβ : Face P T' b₁ b₂ b₃)
    (hd : ∀ w, VertexOf x y z w → ¬ VertexOf b₁ b₂ b₃ w) (hw : VertexOf b₁ b₂ b₃ w) :
    ¬ InTri x y z w ∧ orient x y w ≠ 0 ∧ orient y z w ≠ 0 ∧ orient z x w ≠ 0 := by
  obtain ⟨hx, hy, hz, -, -, -, -, he⟩ := id hα
  obtain ⟨hxy, hyz, hzx⟩ := hα.ne
  have hwP : w ∈ P := by
    rcases hw with rfl | rfl | rfl
    exacts [hβ.1, hβ.2.1, hβ.2.2.1]
  have nv := not_vertex_of_beta hd hw
  unfold VertexOf at nv; push Not at nv
  exact ⟨he w hwP, hP x hx y hy w hwP hxy (Ne.symm nv.1) (Ne.symm nv.2.1),
    hP y hy z hz w hwP hyz (Ne.symm nv.2.1) (Ne.symm nv.2.2),
    hP z hz x hx w hwP hzx (Ne.symm nv.2.2) (Ne.symm nv.1)⟩

/-- The hexagon: with the three ears, the faces cover everything, so `P` has six points. -/
lemma six_points {P : Finset (K × K)} (hP : GenPos P) {A : Finset (Sym2 (K × K))}
    {x y z d₁ d₂ c : K × K} (hα : Face P A x y z) (hD₁ : Face P A y x d₁)
    (hD₂ : Face P A z y d₂) (hD₃ : Face P A x z c)
    (h1 : s(x, d₁) ∈ hullEdges P) (h2 : s(y, d₁) ∈ hullEdges P) (h3 : s(y, d₂) ∈ hullEdges P)
    (h4 : s(z, d₂) ∈ hullEdges P) (h5 : s(z, c) ∈ hullEdges P) (h6 : s(x, c) ∈ hullEdges P) :
    P ⊆ {x, y, z, d₁, d₂, c} := by
  intro q hq
  by_contra hn
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hn
  obtain ⟨qx, qy, qz, qd₁, qd₂, qc⟩ := hn
  obtain ⟨hx, hy, hz, -, -, -, -, he⟩ := id hα
  obtain ⟨hxy, hyz, hzx⟩ := hα.ne
  obtain ⟨-, hxd₁, hd₁y⟩ := hD₁.ne
  obtain ⟨-, hyd₂, hd₂z⟩ := hD₂.ne
  obtain ⟨-, hzc, hcx⟩ := hD₃.ne
  have hd₁P := hD₁.2.2.1; have hd₂P := hD₂.2.2.1; have hcP := hD₃.2.2.1
  have n1 := hP x hx y hy q hq hxy (Ne.symm qx) (Ne.symm qy)
  have n2 := hP y hy z hz q hq hyz (Ne.symm qy) (Ne.symm qz)
  have n3 := hP z hz x hx q hq hzx (Ne.symm qz) (Ne.symm qx)
  have hout : orient x y q < 0 ∨ orient y z q < 0 ∨ orient z x q < 0 := by
    by_contra hc; push Not at hc
    exact he q hq ⟨lt_of_le_of_ne hc.1 (Ne.symm n1), lt_of_le_of_ne hc.2.1 (Ne.symm n2),
      lt_of_le_of_ne hc.2.2 (Ne.symm n3)⟩
  have cyc2 : ∀ a b d : K × K, orient b d a = orient a b d := fun a b d => (orient_cyc a b d).symm
  have cyc3 : ∀ a b d : K × K, orient d a b = orient a b d := fun a b d => by
    rw [orient_cyc a b d, orient_cyc b d a]
  rcases hout with h | h | h
  · refine hD₁.2.2.2.2.2.2.2 q hq ⟨by rw [orient_swap12]; linarith, ?_, ?_⟩
    · exact hull_same_side h1 hy hq hxy.symm hd₁y.symm qx qd₁ (by rw [cyc2]; exact hD₁.2.2.2.1)
    · exact hull_same_side (by rw [Sym2.eq_swap]; exact h2) hx hq hxd₁ hxy qd₁ qy
        (by rw [cyc3]; exact hD₁.2.2.2.1)
  · refine hD₂.2.2.2.2.2.2.2 q hq ⟨by rw [orient_swap12]; linarith, ?_, ?_⟩
    · exact hull_same_side h3 hz hq hyz.symm hd₂z.symm qy qd₂ (by rw [cyc2]; exact hD₂.2.2.2.1)
    · exact hull_same_side (by rw [Sym2.eq_swap]; exact h4) hy hq hyd₂ hyz qd₂ qz
        (by rw [cyc3]; exact hD₂.2.2.2.1)
  · refine hD₃.2.2.2.2.2.2.2 q hq ⟨by rw [orient_swap12]; linarith, ?_, ?_⟩
    · exact hull_same_side h5 hx hq hzx.symm hcx.symm qz qc (by rw [cyc2]; exact hD₃.2.2.2.1)
    · exact hull_same_side (by rw [Sym2.eq_swap]; exact h6) hz hq hzc hzx qc qx
        (by rw [cyc3]; exact hD₃.2.2.2.1)

/-- **The remaining case of Lemma 5.** If every side of `α` meeting `int β` meets exactly three
faces of `B` (in the sense of `NoChain`), and symmetrically, then `|P| ≤ 6`. -/
theorem remaining_small {P : Finset (K × K)} (hP : GenPos P) {A B : Finset (Sym2 (K × K))}
    (hA : IsTri P A) (hB : IsTri P B) (hAB : A ∩ B = hullEdges P) {x y z b₁ b₂ b₃ : K × K}
    (hα : Face P A x y z) (hβ : Face P B b₁ b₂ b₃)
    (hd : ∀ w, VertexOf x y z w → ¬ VertexOf b₁ b₂ b₃ w)
    (hmxy : MeetsSide x y b₁ b₂ b₃) (hmyz : MeetsSide y z b₁ b₂ b₃)
    (NA : ∀ u v o, Rot x y z u v o → MeetsSide u v b₁ b₂ b₃ → NoChain P B u v b₁ b₂ b₃)
    (NB : ∀ u v o, Rot b₁ b₂ b₃ u v o → MeetsSide u v x y z → NoChain P A u v x y z) :
    P.card ≤ 6 := by
  have rotNB : ∀ x' y' z', Rot x y z x' y' z' →
      ∀ u v o, Rot b₁ b₂ b₃ u v o → MeetsSide u v x' y' z' → NoChain P A u v x' y' z' :=
    fun x' y' z' hr u v o hr' hm => noChain_rot hr (NB u v o hr' (meetsSide_rot hr hm))
  have rotd : ∀ x' y' z', Rot x y z x' y' z' → ∀ w, VertexOf x' y' z' w → ¬ VertexOf b₁ b₂ b₃ w :=
    fun x' y' z' hr w hw => hd w (hr.vertexOf.mp hw)
  obtain ⟨d₁, e, f, hd₁, he, hf, hde, hdf, hef, hD₁, hxd₁, hyd₁, cre, crf⟩ :=
    step1 hP hA hB hAB hα hβ hd hmxy (NA x y z (Rot.self _ _ _) hmxy) NB
  obtain ⟨d₂, -, -, hd₂, -, -, -, -, -, hD₂, hyd₂, hzd₂, -, -⟩ :=
    step1 hP hA hB hAB hα.rot hβ (rotd _ _ _ (Rot.one _ _ _)) hmyz
      (NA y z x (Rot.one _ _ _) hmyz) (rotNB _ _ _ (Rot.one _ _ _))
  obtain ⟨hxy, hyz, hzx⟩ := hα.ne
  have h12 : d₁ ≠ d₂ := by
    rintro rfl
    exact hull_two (by rw [Sym2.eq_swap]; exact hxd₁) (by rw [Sym2.eq_swap]; exact hyd₁)
      (by rw [Sym2.eq_swap]; exact hzd₂) hxy hyz hzx
  -- `c`: the vertex of `β` other than `d₁` and `d₂`
  obtain ⟨c, hc, h1c, h2c, hcr⟩ : ∃ c, VertexOf b₁ b₂ b₃ c ∧ d₁ ≠ c ∧ d₂ ≠ c ∧
      Crosses x y d₁ c := by
    rcases three_cover hd₁ he hf hde hdf hef hd₂ with h | h | h
    · exact absurd h.symm h12
    · subst h; exact ⟨f, hf, hdf, hef, crf⟩
    · subst h; exact ⟨e, he, hde, Ne.symm hef, cre⟩
  have step1zx : MeetsSide z x b₁ b₂ b₃ →
      ∃ d₃, Face P A x z d₃ ∧ s(z, d₃) ∈ hullEdges P ∧ s(x, d₃) ∈ hullEdges P := by
    intro hm
    obtain ⟨d₃, -, -, -, -, -, -, -, -, hD₃, h1, h2, -, -⟩ :=
      step1 hP hA hB hAB hα.rot.rot hβ (rotd _ _ _ (Rot.two _ _ _)) hm
        (NA z x y (Rot.two _ _ _) hm) (rotNB _ _ _ (Rot.two _ _ _))
    exact ⟨d₃, hD₃, h1, h2⟩
  obtain ⟨hD₃, hzc, hxc⟩ :=
    step3 hP hA hα hβ hd NB hd₁ hd₂ hc h12 h1c h2c hD₁ hD₂ hcr step1zx
  calc P.card ≤ ({x, y, z, d₁, d₂, c} : Finset (K × K)).card :=
        Finset.card_le_card (six_points hP hα hD₁ hD₂ hD₃ hxd₁ hyd₁ hyd₂ hzd₂ hzc hxc)
    _ ≤ 6 := Finset.card_le_six

/-- **Lemma 5 (Regeneration).** -/
theorem regeneration {P : Finset (K × K)} (hP : GenPos P) (h7 : 7 ≤ P.card)
    {A B : Finset (Sym2 (K × K))} (hA : IsTri P A) (hB : IsTri P B)
    (hAB : A ∩ B = hullEdges P) {x y z b₁ b₂ b₃ p : K × K} (hα : Face P A x y z)
    (hβ : Face P B b₁ b₂ b₃) (hd : ∀ w, VertexOf x y z w → ¬ VertexOf b₁ b₂ b₃ w)
    (hpα : InTri x y z p) (hpβ : InTri b₁ b₂ b₃ p) :
    GoodPair (insert p P) (star A p x y z) (star B p b₁ b₂ b₃) := by
  by_contra hng
  have memA : ∀ u, VertexOf x y z u → s(p, u) ∈ star A p x y z := by
    rintro u (rfl | rfl | rfl) <;> simp [star]
  have memB : ∀ u, VertexOf b₁ b₂ b₃ u → s(p, u) ∈ star B p b₁ b₂ b₃ := by
    rintro u (rfl | rfl | rfl) <;> simp [star]
  have NA : ∀ u v o, Rot x y z u v o → MeetsSide u v b₁ b₂ b₃ → NoChain P B u v b₁ b₂ b₃ := by
    intro u v o hrot hm t₁ t₂ t₃ hT hmT hTne
    by_contra hn
    push Not at hn
    apply hng
    refine good_of_chain hP (hrot.face hα) (hrot.inTri hpα) Finset.subset_union_left
      (memA u (hrot.vertexOf.mp (Or.inl rfl))) (memA v (hrot.vertexOf.mp (Or.inr (Or.inl rfl))))
      hβ hpβ Finset.subset_union_left hB.nonCross hT hTne (fun w hw => ⟨?_, ?_⟩) hmT
    · rintro rfl; exact hn.1 hw
    · rintro rfl; exact hn.2 hw
  have NB : ∀ u v o, Rot b₁ b₂ b₃ u v o → MeetsSide u v x y z → NoChain P A u v x y z := by
    intro u v o hrot hm t₁ t₂ t₃ hT hmT hTne
    by_contra hn
    push Not at hn
    apply hng
    refine (good_of_chain hP (hrot.face hβ) (hrot.inTri hpβ) Finset.subset_union_left
      (memB u (hrot.vertexOf.mp (Or.inl rfl))) (memB v (hrot.vertexOf.mp (Or.inr (Or.inl rfl))))
      hα hpα Finset.subset_union_left hA.nonCross hT hTne (fun w hw => ⟨?_, ?_⟩) hmT).symm
    · rintro rfl; exact hn.1 hw
    · rintro rfl; exact hn.2 hw
  obtain ⟨x', y', z', hr, hm1, hm2⟩ := prop_b hP hα hβ hd hpα hpβ
  have := remaining_small hP hA hB hAB (hr.face hα) hβ (fun w hw => hd w (hr.vertexOf.mp hw))
    hm1 hm2 (fun u v o hr' hm => NA u v o (hr.trans hr') hm)
    (fun u v o hr' hm => noChain_rot hr (NB u v o hr' (meetsSide_rot hr hm)))
  omega

end TwoTri
