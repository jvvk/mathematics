import LeanProofs.TwoTri.Regen5b

/-!
# Lemma 5 (Regeneration): Steps 2 and 3 and the full statement
-/

set_option linter.unusedSectionVars false

namespace TwoTri

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

lemma Rot.symm {x y z u v o : K × K} (h : Rot x y z u v o) : Rot u v o x y z := by
  unfold Rot at *
  rcases h with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;> tauto

lemma meetsSide_rot {u v x y z x' y' z' : K × K} (h : Rot x y z x' y' z')
    (hm : MeetsSide u v x' y' z') : MeetsSide u v x y z := by
  obtain ⟨s, h0, h1, hin⟩ := hm
  exact ⟨s, h0, h1, h.symm.inTri hin⟩

lemma noChain_rot {P : Finset (K × K)} {T : Finset (Sym2 (K × K))} {u v x y z x' y' z' : K × K}
    (h : Rot x y z x' y' z') (hn : NoChain P T u v x y z) : NoChain P T u v x' y' z' := by
  intro t₁ t₂ t₃ hf hm ⟨w, hw, hnw⟩
  exact hn t₁ t₂ t₃ hf hm ⟨w, hw, fun h' => hnw (h.vertexOf.mpr h')⟩

lemma three_cover {b₁ b₂ b₃ d e f w : K × K} (hd : VertexOf b₁ b₂ b₃ d)
    (he : VertexOf b₁ b₂ b₃ e) (hf : VertexOf b₁ b₂ b₃ f) (hde : d ≠ e) (hdf : d ≠ f)
    (hef : e ≠ f) (hw : VertexOf b₁ b₂ b₃ w) : w = d ∨ w = e ∨ w = f := by
  unfold VertexOf at *
  rcases hd with rfl | rfl | rfl <;> rcases he with rfl | rfl | rfl <;>
    rcases hf with rfl | rfl | rfl <;> rcases hw with rfl | rfl | rfl <;> simp_all

/-- Two distinct vertices of a triangle span one of its sides, in one of the two orders. -/
lemma side_of_two {b₁ b₂ b₃ a b : K × K} (ha : VertexOf b₁ b₂ b₃ a) (hb : VertexOf b₁ b₂ b₃ b)
    (hab : a ≠ b) : ∃ o, Rot b₁ b₂ b₃ a b o ∨ Rot b₁ b₂ b₃ b a o := by
  unfold VertexOf at ha hb
  rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
  all_goals first
    | exact absurd rfl hab
    | exact ⟨_, Or.inl (Rot.self _ _ _)⟩ | exact ⟨_, Or.inl (Rot.one _ _ _)⟩
    | exact ⟨_, Or.inl (Rot.two _ _ _)⟩ | exact ⟨_, Or.inr (Rot.self _ _ _)⟩
    | exact ⟨_, Or.inr (Rot.one _ _ _)⟩ | exact ⟨_, Or.inr (Rot.two _ _ _)⟩

/-- `NoChain` for an unordered side of `β`. -/
lemma noChain_side {P : Finset (K × K)} {A : Finset (Sym2 (K × K))} {x y z b₁ b₂ b₃ a b : K × K}
    (NB : ∀ u v o, Rot b₁ b₂ b₃ u v o → MeetsSide u v x y z → NoChain P A u v x y z)
    (ha : VertexOf b₁ b₂ b₃ a) (hb : VertexOf b₁ b₂ b₃ b) (hab : a ≠ b)
    (hm : MeetsSide a b x y z) : NoChain P A a b x y z := by
  obtain ⟨o, h | h⟩ := side_of_two ha hb hab
  · exact NB a b o h hm
  · exact (NB b a o h (meetsSide_swap hm)).swap

lemma not_vertex_of_beta {x y z b₁ b₂ b₃ w : K × K}
    (hd : ∀ w, VertexOf x y z w → ¬ VertexOf b₁ b₂ b₃ w) (hw : VertexOf b₁ b₂ b₃ w) :
    ¬ VertexOf x y z w := fun h => hd w h hw

/-- **Step 3.** The side `d₁ c` of `β` enters `α` across `xy` and leaves across `zx`, the face of
`A` beyond `zx` is `x z c`, and `zc`, `xc` are hull edges. -/
theorem step3 {P : Finset (K × K)} (hP : GenPos P) {A B : Finset (Sym2 (K × K))}
    (hA : IsTri P A) {x y z b₁ b₂ b₃ d₁ d₂ c : K × K} (hα : Face P A x y z)
    (hβ : Face P B b₁ b₂ b₃) (hd : ∀ w, VertexOf x y z w → ¬ VertexOf b₁ b₂ b₃ w)
    (NB : ∀ u v o, Rot b₁ b₂ b₃ u v o → MeetsSide u v x y z → NoChain P A u v x y z)
    (hd₁ : VertexOf b₁ b₂ b₃ d₁) (hd₂ : VertexOf b₁ b₂ b₃ d₂) (hc : VertexOf b₁ b₂ b₃ c)
    (h12 : d₁ ≠ d₂) (h1c : d₁ ≠ c) (h2c : d₂ ≠ c)
    (hD₁ : Face P A y x d₁) (hD₂ : Face P A z y d₂) (hcross : Crosses x y d₁ c)
    (step1zx : MeetsSide z x b₁ b₂ b₃ →
      ∃ d₃, Face P A x z d₃ ∧ s(z, d₃) ∈ hullEdges P ∧ s(x, d₃) ∈ hullEdges P) :
    Face P A x z c ∧ s(z, c) ∈ hullEdges P ∧ s(x, c) ∈ hullEdges P := by
  obtain ⟨s, σ, hs0, hs1, hσ0, hσ1, hcr⟩ := hcross
  obtain ⟨hx, hy, hz, hαD, -, -, hzxA, hαe⟩ := id hα
  obtain ⟨hxy, hyz, hzx⟩ := hα.ne
  have hβP : ∀ w, VertexOf b₁ b₂ b₃ w → w ∈ P := by
    rintro w (rfl | rfl | rfl)
    exacts [hβ.1, hβ.2.1, hβ.2.2.1]
  have hd₁P := hβP d₁ hd₁; have hcP := hβP c hc
  have nα : ∀ w, VertexOf b₁ b₂ b₃ w → w ≠ x ∧ w ≠ y ∧ w ≠ z := fun w hw => by
    have := not_vertex_of_beta hd hw
    unfold VertexOf at this; push Not at this
    exact ⟨this.1, this.2.1, this.2.2⟩
  obtain ⟨d₁x, d₁y, d₁z⟩ := nα d₁ hd₁
  obtain ⟨cx, cy, cz⟩ := nα c hc
  have hX := cross_of_common hP hx hy hd₁P hcP hxy h1c
    (fun e => by
      rcases Sym2.eq_iff.mp e with ⟨h, -⟩ | ⟨h, -⟩
      · exact d₁x h.symm
      · exact cx h.symm) hs0 hs1 hσ0.le hσ1.le hcr
  have hd₁neg : orient x y d₁ < 0 := by
    have := hD₁.2.2.2.1; rw [orient_swap12] at this; linarith
  have hcpos : 0 < orient x y c := by nlinarith [hX.1]
  -- a point of `d₁ c` inside `α`
  obtain ⟨ε, hε0, hε1, hw0⟩ := near_side hαD hs0 hs1 hcpos
  obtain ⟨σ', hσ'0, hσ'1, hw0eq⟩ := toward_end hσ0 hσ1 hε0 hε1 hcr c (Or.inr rfl)
  set w0 := lerp (lerp x y s) c ε
  have NC : NoChain P A d₁ c x y z := noChain_side NB hd₁ hc h1c ⟨σ', hσ'0, hσ'1, hw0eq ▸ hw0⟩
  have hout : orient x y c < 0 ∨ orient y z c < 0 ∨ orient z x c < 0 := by
    have n2 := hP y hy z hz c hcP hyz (Ne.symm cy) (Ne.symm cz)
    have n3 := hP z hz x hx c hcP hzx (Ne.symm cz) (Ne.symm cx)
    by_contra hn; push Not at hn
    exact hαe c hcP ⟨hcpos, lt_of_le_of_ne hn.2.1 (Ne.symm n2), lt_of_le_of_ne hn.2.2 (Ne.symm n3)⟩
  obtain ⟨t, ht0, ht1, hcase⟩ := exit' hw0 hout
  obtain ⟨σ₂, hσ₂0, hσ₂1, hmeq⟩ := toward_end hσ'0 hσ'1 ht0 ht1 hw0eq c (Or.inr rfl)
  set m := lerp w0 c t
  have hmc : orient d₁ c m = 0 := by rw [hmeq, orient_lerp_self]
  -- the exit point lies beyond the side it crosses
  have beyond : ∀ u v : K × K, 0 < orient u v w0 → orient u v m = 0 → orient u v c < 0 := by
    intro u v h1 h2
    have : (1 - t) * orient u v w0 + t * orient u v c = 0 := by rw [← orient_lerp]; exact h2
    nlinarith
  -- `d₁` is on the side of `α` of any side line that `d₁ c` crosses at `m`
  have before : ∀ u v : K × K, orient u v m = 0 → orient u v c < 0 → 0 < orient u v d₁ := by
    intro u v h0 hneg
    have : (1 - σ₂) * orient u v d₁ + σ₂ * orient u v c = 0 := by rw [← orient_lerp, ← hmeq]; exact h0
    nlinarith
  rcases hcase with hv | ⟨u, v, o, hrot, h0, hp1, hp2⟩
  · exfalso
    have key : ∀ w, VertexOf x y z w → m = w → False := by
      intro w hw hm
      have hwP : w ∈ P := by rcases hw with rfl | rfl | rfl <;> assumption
      rw [hm] at hmc
      rcases hP.on_line hd₁P hcP hwP h1c hmc with h | h
      · exact hd w hw (h ▸ hd₁)
      · exact hd w hw (h ▸ hc)
    rcases hv with hv | hv | hv
    exacts [key x (Or.inl rfl) hv, key y (Or.inr (Or.inl rfl)) hv, key z (Or.inr (Or.inr rfl)) hv]
  · rcases hrot with ⟨e1, e2, e3⟩ | ⟨e1, e2, e3⟩ | ⟨e1, e2, e3⟩ <;> rw [e1, e2] at h0 <;>
      rw [e2, e3] at hp1 <;> rw [e3, e1] at hp2
    · exfalso
      have : 0 < orient x y m := by
        rw [orient_lerp]; nlinarith [hw0.1]
      linarith
    · -- exit across `yz`: the face beyond is `z y d₂`, which cannot meet `d₁ c`
      exfalso
      have hcneg := beyond y z hw0.2.1 h0
      obtain ⟨ρ, hρ0, hρ1, hmρ⟩ := on_side h0 hp1 hp2
      have hmρ' : m = lerp z y (1 - ρ) := by rw [hmρ, ← lerp_symm]
      obtain ⟨ε', hε'0, hε'1, hin⟩ := near_side hD₂.2.2.2.1 (σ := 1 - ρ) (by linarith)
        (by linarith) (q := c) (by rw [orient_swap12]; linarith)
      rw [← hmρ'] at hin
      obtain ⟨σ₃, h30, h31, h3⟩ := toward_end hσ₂0 hσ₂1 hε'0 hε'1 hmeq c (Or.inr rfl)
      obtain ⟨-, hd₂y, hd₂z⟩ := hD₂.ne
      have := NC z y d₂ hD₂ ⟨σ₃, h30, h31, h3 ▸ hin⟩ ⟨d₂, Or.inr (Or.inr rfl),
        not_vertex_of_beta hd hd₂⟩
      rcases this with (h | h | h) | (h | h | h)
      exacts [d₁z h, d₁y h, h12 h, cz h, cy h, h2c h.symm]
    · -- exit across `zx`
      have hcneg := beyond z x hw0.2.2 h0
      have hd₁pos := before z x h0 hcneg
      obtain ⟨ρ, hρ0, hρ1, hmρ⟩ := on_side h0 hp1 hp2
      have hmρ' : m = lerp x z (1 - ρ) := by rw [hmρ, ← lerp_symm]
      obtain ⟨t₃, ht₃, hF⟩ := side_face hP hA hx hz (by rw [Sym2.eq_swap]; exact hzxA)
        ⟨c, hcP, by rw [orient_swap12]; linarith⟩
      obtain ⟨ε', hε'0, hε'1, hin⟩ := near_side hF.2.2.2.1 (σ := 1 - ρ) (by linarith)
        (by linarith) (q := c) (by rw [orient_swap12]; linarith)
      rw [← hmρ'] at hin
      obtain ⟨σ₃, h30, h31, h3⟩ := toward_end hσ₂0 hσ₂1 hε'0 hε'1 hmeq c (Or.inr rfl)
      obtain ⟨-, ht₃z, ht₃x⟩ := hF.ne
      have ht₃y : t₃ ≠ y := by
        rintro rfl
        have := hF.2.2.2.1
        have h2 : orient x z t₃ = -orient x t₃ z := orient_swap23 _ _ _
        rw [h2] at this; linarith
      have := NC x z t₃ hF ⟨σ₃, h30, h31, h3 ▸ hin⟩ ⟨t₃, Or.inr (Or.inr rfl), by
        rintro (h | h | h)
        exacts [ht₃x h, ht₃y h, ht₃z.symm h]⟩
      have ht₃c : t₃ = c := by
        rcases this with (h | h | h) | (h | h | h)
        · exact absurd h d₁x
        · exact absurd h d₁z
        · exfalso
          have := hF.2.2.2.1
          rw [← h, orient_swap12] at this; linarith
        · exact absurd h cx
        · exact absurd h cz
        · exact h.symm
      rw [ht₃c] at hF
      -- `zx` meets the interior of `β`
      have hmβ : MeetsSide z x b₁ b₂ b₃ := by
        obtain ⟨o, hr | hr⟩ := side_of_two hd₁ hc h1c
        · have hβ' := hr.face hβ
          have hX' := cross_of_common hP hz hx hd₁P hcP hzx h1c
            (fun e => by
              rcases Sym2.eq_iff.mp e with ⟨h, -⟩ | ⟨h, -⟩
              · exact d₁z h.symm
              · exact cz h.symm) hρ0 hρ1 hσ₂0.le hσ₂1.le (hmρ.symm.trans hmeq)
          have hsep := hX'.2
          have pick : ∃ q, (q = z ∨ q = x) ∧ 0 < orient d₁ c q := by
            rcases lt_or_gt_of_ne (show orient d₁ c z ≠ 0 from fun h0 => by
              rw [h0, zero_mul] at hsep; exact lt_irrefl _ hsep) with h | h
            · exact ⟨x, Or.inr rfl, by nlinarith⟩
            · exact ⟨z, Or.inl rfl, h⟩
          obtain ⟨q, hq, hqp⟩ := pick
          obtain ⟨ε'', h0'', h1'', hin''⟩ := near_side hβ'.2.2.2.1 hσ₂0 hσ₂1 hqp
          rw [← hmeq, hmρ] at hin''
          obtain ⟨σ₄, h40, h41, h4⟩ := toward_end hρ0 hρ1 h0'' h1'' rfl q hq
          exact ⟨σ₄, h40, h41, hr.symm.inTri (h4 ▸ hin'')⟩
        · have hβ' := hr.face hβ
          have hmeq' : m = lerp c d₁ (1 - σ₂) := by rw [hmeq, ← lerp_symm]
          have hX' := cross_of_common hP hz hx hcP hd₁P hzx (Ne.symm h1c)
            (fun e => by
              rcases Sym2.eq_iff.mp e with ⟨h, -⟩ | ⟨h, -⟩
              · exact cz h.symm
              · exact d₁z h.symm) hρ0 hρ1 (by linarith) (by linarith)
            (hmρ.symm.trans hmeq')
          have hsep := hX'.2
          have pick : ∃ q, (q = z ∨ q = x) ∧ 0 < orient c d₁ q := by
            rcases lt_or_gt_of_ne (show orient c d₁ z ≠ 0 from fun h0 => by
              rw [h0, zero_mul] at hsep; exact lt_irrefl _ hsep) with h | h
            · exact ⟨x, Or.inr rfl, by nlinarith⟩
            · exact ⟨z, Or.inl rfl, h⟩
          obtain ⟨q, hq, hqp⟩ := pick
          obtain ⟨ε'', h0'', h1'', hin''⟩ := near_side hβ'.2.2.2.1 (σ := 1 - σ₂) (by linarith)
            (by linarith) hqp
          rw [← hmeq', hmρ] at hin''
          obtain ⟨σ₄, h40, h41, h4⟩ := toward_end hρ0 hρ1 h0'' h1'' rfl q hq
          exact ⟨σ₄, h40, h41, hr.symm.inTri (h4 ▸ hin'')⟩
      obtain ⟨d₃, hD₃, h1, h2⟩ := step1zx hmβ
      have := face_unique hP hA.nonCross hF hD₃
      rw [this] at h1 h2
      exact ⟨hF, h1, h2⟩

end TwoTri
