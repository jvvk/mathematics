import LeanProofs.TwoTri.Oct

/-!
# Lemma 5 (Regeneration), in the paper's generality

Definitions, helper lemmas and property (b).
-/

set_option linter.unusedSectionVars false

namespace TwoTri

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- `w` is a vertex of the triangle `a b c`. -/
def VertexOf (a b c w : K × K) : Prop := w = a ∨ w = b ∨ w = c

/-- The open segment `uv` meets the interior of the triangle `a b c`. -/
def MeetsSide (u v a b c : K × K) : Prop := ∃ s : K, 0 < s ∧ s < 1 ∧ InTri a b c (lerp u v s)

/-- Two triangulations have a good pair of faces. -/
def GoodPair (P : Finset (K × K)) (A B : Finset (Sym2 (K × K))) : Prop :=
  ∃ x y z b₁ b₂ b₃ : K × K, Face P A x y z ∧ Face P B b₁ b₂ b₃ ∧
    (∀ w, VertexOf x y z w → ¬ VertexOf b₁ b₂ b₃ w) ∧
    ∃ r, InTri x y z r ∧ InTri b₁ b₂ b₃ r

lemma Rot.inTri {x y z u v o r : K × K} (h : Rot x y z u v o) (hr : InTri x y z r) :
    InTri u v o r := by
  rcases h with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  exacts [hr, hr.rot, hr.rot.rot]

lemma Rot.face {P : Finset (K × K)} {T : Finset (Sym2 (K × K))} {x y z u v o : K × K}
    (h : Rot x y z u v o) (hf : Face P T x y z) : Face P T u v o := by
  rcases h with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  exacts [hf, hf.rot, hf.rot.rot]

lemma Rot.vertexOf {x y z u v o w : K × K} (h : Rot x y z u v o) :
    VertexOf u v o w ↔ VertexOf x y z w := by
  unfold VertexOf
  rcases h with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;> tauto

lemma Rot.self (x y z : K × K) : Rot x y z x y z := Or.inl ⟨rfl, rfl, rfl⟩
lemma Rot.one (x y z : K × K) : Rot x y z y z x := Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)
lemma Rot.two (x y z : K × K) : Rot x y z z x y := Or.inr (Or.inr ⟨rfl, rfl, rfl⟩)

lemma Rot.trans {x y z u v o u' v' o' : K × K} (h1 : Rot x y z u v o) (h2 : Rot u v o u' v' o') :
    Rot x y z u' v' o' := by
  unfold Rot at *
  rcases h1 with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
    rcases h2 with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;> tauto

lemma GoodPair.symm {P : Finset (K × K)} {A B : Finset (Sym2 (K × K))} (h : GoodPair P A B) :
    GoodPair P B A := by
  obtain ⟨x, y, z, b₁, b₂, b₃, hα, hβ, hd, r, h1, h2⟩ := h
  exact ⟨b₁, b₂, b₃, x, y, z, hβ, hα, fun w hw hw' => hd w hw' hw, r, h2, h1⟩

/-- Points of a hull edge's line: every other point is on the same side. -/
lemma hull_same_side {P : Finset (K × K)} {a b c q : K × K} (h : s(a, b) ∈ hullEdges P)
    (hc : c ∈ P) (hq : q ∈ P) (hca : c ≠ a) (hcb : c ≠ b) (hqa : q ≠ a) (hqb : q ≠ b)
    (hpos : 0 < orient a b c) : 0 < orient a b q := by
  obtain ⟨-, -, -, hh⟩ := mk_mem_hullEdges.mp h
  rcases hh with h | h
  · exact h q hq hqa hqb
  · have := h c hc hca hcb; linarith

/-- A point has at most two hull neighbours. -/
lemma hull_two {P : Finset (K × K)} {d x y z : K × K} (hx : s(d, x) ∈ hullEdges P)
    (hy : s(d, y) ∈ hullEdges P) (hz : s(d, z) ∈ hullEdges P) (hxy : x ≠ y) (hyz : y ≠ z)
    (hzx : z ≠ x) : False := by
  obtain ⟨-, hxP, hdx, h1⟩ := mk_mem_hullEdges.mp hx
  obtain ⟨-, hyP, hdy, h2⟩ := mk_mem_hullEdges.mp hy
  obtain ⟨-, hzP, hdz, h3⟩ := mk_mem_hullEdges.mp hz
  rw [hullP_iff] at h1 h2 h3
  -- two hull edges of the same type at `d` contradict each other
  have same1 : ∀ u w, u ∈ P → w ∈ P → d ≠ u → d ≠ w → u ≠ w → HullPos P d u → HullPos P d w →
      False := by
    intro u w hu hw hdu hdw huw e1 e2
    have a1 := e1 w hw (Ne.symm hdw) (Ne.symm huw)
    have a2 := e2 u hu (Ne.symm hdu) huw
    rw [orient_swap23] at a2; linarith
  have same2 : ∀ u w, u ∈ P → w ∈ P → d ≠ u → d ≠ w → u ≠ w → HullPos P u d → HullPos P w d →
      False := by
    intro u w hu hw hdu hdw huw e1 e2
    have a1 := e1 w hw (Ne.symm huw) (Ne.symm hdw)
    have a2 := e2 u hu huw (Ne.symm hdu)
    rw [orient_cyc, orient_swap23] at a1
    rw [orient_cyc] at a2
    linarith
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> rcases h3 with h3 | h3
  · exact same1 x y hxP hyP hdx hdy hxy h1 h2
  · exact same1 x y hxP hyP hdx hdy hxy h1 h2
  · exact same1 x z hxP hzP hdx hdz (Ne.symm hzx) h1 h3
  · exact same2 y z hyP hzP hdy hdz hyz h2 h3
  · exact same1 y z hyP hzP hdy hdz hyz h2 h3
  · exact same2 x z hxP hzP hdx hdz (Ne.symm hzx) h1 h3
  · exact same2 x y hxP hyP hdx hdy hxy h1 h2
  · exact same2 x y hxP hyP hdx hdy hxy h1 h2

/-- Leaving one face from a common interior point towards a vertex of the other crosses a side
of the first at a point inside the second. -/
lemma exit_to_vertex {P : Finset (K × K)} (hP : GenPos P) {T : Finset (Sym2 (K × K))}
    {T' : Finset (Sym2 (K × K))} {x y z b₁ b₂ b₃ r : K × K} (hα : Face P T x y z)
    (hβ : Face P T' b₁ b₂ b₃) (hd : ∀ w, VertexOf x y z w → ¬ VertexOf b₁ b₂ b₃ w)
    (hr : InTri x y z r) (hr' : InTri b₁ b₂ b₃ r) :
    ∃ u v o, Rot x y z u v o ∧ MeetsSide u v b₁ b₂ b₃ ∧ orient u v b₁ < 0 := by
  obtain ⟨hx, hy, hz, hD, -, -, -, he⟩ := id hα
  obtain ⟨hb1, hb2, hb3, hD', -, -, -, he'⟩ := id hβ
  obtain ⟨hxy, hyz, hzx⟩ := hα.ne
  have nb : ¬ VertexOf x y z b₁ := fun h => hd b₁ h (Or.inl rfl)
  have hout : orient x y b₁ < 0 ∨ orient y z b₁ < 0 ∨ orient z x b₁ < 0 := by
    unfold VertexOf at nb; push Not at nb
    have n1 := hP x hx y hy b₁ hb1 hxy (Ne.symm nb.1) (Ne.symm nb.2.1)
    have n2 := hP y hy z hz b₁ hb1 hyz (Ne.symm nb.2.1) (Ne.symm nb.2.2)
    have n3 := hP z hz x hx b₁ hb1 hzx (Ne.symm nb.2.2) (Ne.symm nb.1)
    by_contra hc; push Not at hc
    exact he b₁ hb1 ⟨lt_of_le_of_ne hc.1 (Ne.symm n1), lt_of_le_of_ne hc.2.1 (Ne.symm n2),
      lt_of_le_of_ne hc.2.2 (Ne.symm n3)⟩
  obtain ⟨t, ht0, ht1, hcase⟩ := exit' hr hout
  -- points of the open segment `r b₁` are inside `β`
  have hin : InTri b₁ b₂ b₃ (lerp r b₁ t) := hr'.lerp_vertex (Or.inl rfl) ht0.le ht1
  rcases hcase with hv | ⟨u, v, o, hrot, h0, hp1, hp2⟩
  · exfalso
    rcases hv with hv | hv | hv
    · exact he' x hx (hv ▸ hin)
    · exact he' y hy (hv ▸ hin)
    · exact he' z hz (hv ▸ hin)
  · obtain ⟨σ, hσ0, hσ1, hm⟩ := on_side h0 hp1 hp2
    refine ⟨u, v, o, hrot, ⟨σ, hσ0, hσ1, hm ▸ hin⟩, ?_⟩
    have hru : 0 < orient u v r := (hrot.inTri hr).1
    have E : (1 - t) * orient u v r + t * orient u v b₁ = 0 := by rw [← orient_lerp]; exact h0
    nlinarith

/-- **Property (b).** If the interiors of faces `xyz` and `β` with no common vertex meet, two
sides of `xyz` (consecutive after a rotation) meet the interior of `β`. -/
theorem prop_b {P : Finset (K × K)} (hP : GenPos P) {T T' : Finset (Sym2 (K × K))}
    {x y z b₁ b₂ b₃ r : K × K} (hα : Face P T x y z) (hβ : Face P T' b₁ b₂ b₃)
    (hd : ∀ w, VertexOf x y z w → ¬ VertexOf b₁ b₂ b₃ w)
    (hr : InTri x y z r) (hr' : InTri b₁ b₂ b₃ r) :
    ∃ u v o, Rot x y z u v o ∧ MeetsSide u v b₁ b₂ b₃ ∧ MeetsSide v o b₁ b₂ b₃ := by
  have hd2 : ∀ w, VertexOf x y z w → ¬ VertexOf b₂ b₃ b₁ w := fun w hw hw' =>
    hd w hw ((Rot.one b₁ b₂ b₃).vertexOf.mp hw')
  have hd3 : ∀ w, VertexOf x y z w → ¬ VertexOf b₃ b₁ b₂ w := fun w hw hw' =>
    hd w hw ((Rot.two b₁ b₂ b₃).vertexOf.mp hw')
  obtain ⟨u₁, v₁, o₁, r₁, m₁, n₁⟩ := exit_to_vertex hP hα hβ hd hr hr'
  obtain ⟨u₂, v₂, o₂, r₂, m₂, n₂⟩ := exit_to_vertex hP hα hβ.rot hd2 hr hr'.rot
  obtain ⟨u₃, v₃, o₃, r₃, m₃, n₃⟩ := exit_to_vertex hP hα hβ.rot.rot hd3 hr hr'.rot.rot
  have M : ∀ u v, MeetsSide u v b₂ b₃ b₁ → MeetsSide u v b₁ b₂ b₃ := by
    rintro u v ⟨s, h0, h1, h⟩; exact ⟨s, h0, h1, h.rot.rot⟩
  have M' : ∀ u v, MeetsSide u v b₃ b₁ b₂ → MeetsSide u v b₁ b₂ b₃ := by
    rintro u v ⟨s, h0, h1, h⟩; exact ⟨s, h0, h1, h.rot⟩
  -- not all three exits through the same side
  have hDb := hr'.ccw
  have notall : ∀ u v o, Rot x y z u v o → orient u v b₁ < 0 → orient u v b₂ < 0 →
      orient u v b₃ < 0 → False := by
    intro u v o hrot e1 e2 e3
    have B := orient_bary b₁ b₂ b₃ r u v
    have := (hrot.inTri hr).1
    nlinarith [mul_pos hr'.2.1 (neg_pos.mpr e1), mul_pos hr'.2.2 (neg_pos.mpr e2),
      mul_pos hr'.1 (neg_pos.mpr e3)]
  -- from two different exit sides, a rotation with two consecutive meeting sides
  have pick : ∀ u v o u' v' o', Rot x y z u v o → Rot x y z u' v' o' → ¬ (u = u' ∧ v = v') →
      MeetsSide u v b₁ b₂ b₃ → MeetsSide u' v' b₁ b₂ b₃ →
      ∃ u v o, Rot x y z u v o ∧ MeetsSide u v b₁ b₂ b₃ ∧ MeetsSide v o b₁ b₂ b₃ := by
    intro u v o u' v' o' h h' hne hm hm'
    rcases h with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases h' with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    all_goals first
      | exact absurd ⟨rfl, rfl⟩ hne
      | exact ⟨_, _, _, Rot.self _ _ _, hm, hm'⟩
      | exact ⟨_, _, _, Rot.one _ _ _, hm, hm'⟩
      | exact ⟨_, _, _, Rot.two _ _ _, hm, hm'⟩
      | exact ⟨_, _, _, Rot.self _ _ _, hm', hm⟩
      | exact ⟨_, _, _, Rot.one _ _ _, hm', hm⟩
      | exact ⟨_, _, _, Rot.two _ _ _, hm', hm⟩
  by_cases h12 : u₁ = u₂ ∧ v₁ = v₂
  · by_cases h13 : u₁ = u₃ ∧ v₁ = v₃
    · exfalso
      obtain ⟨rfl, rfl⟩ := h12
      obtain ⟨rfl, rfl⟩ := h13
      exact notall u₁ v₁ o₁ r₁ n₁ n₂ n₃
    · exact pick _ _ _ _ _ _ r₁ r₃ h13 m₁ (M' _ _ m₃)
  · exact pick _ _ _ _ _ _ r₁ r₂ h12 m₁ (M _ _ m₂)

end TwoTri
