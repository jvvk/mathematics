import LeanProofs.TwoTri.Exit

/-!
# Faces of a non-crossing set

Two faces of the same non-crossing set whose interiors meet are the same triangle; and a segment
from a generic point inside a triangle to a point of the set outside it crosses a side.
-/

set_option linter.unusedSectionVars false

namespace TwoTri

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- The non-crossing part of being a triangulation. -/
def NonCross (T : Finset (Sym2 (K × K))) : Prop := ∀ s ∈ T, ∀ t ∈ T, ¬ Cross s t

lemma IsTri.nonCross {P : Finset (K × K)} {T : Finset (Sym2 (K × K))} (h : IsTri P T) :
    NonCross T := h.2.1

/-- A side of a face, as an element of the edge set. -/
lemma Face.side_mem {P : Finset (K × K)} {T : Finset (Sym2 (K × K))} {x y z : K × K}
    (h : Face P T x y z) {s : Sym2 (K × K)}
    (hs : s = s(x, y) ∨ s = s(y, z) ∨ s = s(z, x)) : s ∈ T := by
  rcases hs with rfl | rfl | rfl
  exacts [h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1]

/-- The side `uv` of a face cannot pass through the interior of another face. -/
lemma side_not_through {P : Finset (K × K)} (hP : GenPos P) {T : Finset (Sym2 (K × K))}
    (hT : NonCross T) {a b c u v : K × K} (hf : Face P T a b c) (hu : u ∈ P) (hv : v ∈ P)
    (huv : u ≠ v) (hs : s(u, v) ∈ T) {σ : K} (hσ0 : 0 < σ) (hσ1 : σ < 1)
    (hin : InTri a b c (lerp u v σ)) : False := by
  obtain ⟨ha, hb, hc, -, -, -, -, he⟩ := id hf
  obtain ⟨u', v', hside, hx⟩ :=
    through hP ha hb hc hu hv huv (he u hu) (he v hv) hσ0 hσ1 hin
  exact hT _ hs _ (hf.side_mem hside) (cross_mk.mpr hx)

/-- If the interiors of two faces of a non-crossing set meet, a vertex of the second that is not
a vertex of the first leads to a crossing. -/
lemma faces_key {P : Finset (K × K)} (hP : GenPos P) {T : Finset (Sym2 (K × K))}
    (hT : NonCross T) {x y z a b c r : K × K} (hf : Face P T x y z) (hg : Face P T a b c)
    (hax : a ≠ x) (hay : a ≠ y) (haz : a ≠ z) (hr1 : InTri x y z r) (hr2 : InTri a b c r) :
    False := by
  obtain ⟨hx, hy, hz, hD, -, -, -, he⟩ := id hf
  obtain ⟨ha, hb, hc, hD2, -, -, -, he2⟩ := id hg
  obtain ⟨hxy, hyz, hzx⟩ := hf.ne
  have n1 : orient x y a ≠ 0 := hP x hx y hy a ha hxy (Ne.symm hax) (Ne.symm hay)
  have n2 : orient y z a ≠ 0 := hP y hy z hz a ha hyz (Ne.symm hay) (Ne.symm haz)
  have n3 : orient z x a ≠ 0 := hP z hz x hx a ha hzx (Ne.symm haz) (Ne.symm hax)
  obtain ⟨t, ht0, ht1, hcase⟩ := exit hr1 n1 n2 n3 (he a ha)
  have hin : InTri a b c (lerp r a t) := by
    obtain ⟨r1, r2, r3⟩ := hr2
    have hbca : orient b c a = orient a b c := (orient_cyc a b c).symm
    refine ⟨?_, ?_, ?_⟩ <;> rw [orient_lerp]
    · simp only [orient_self13, mul_zero, add_zero]; nlinarith
    · rw [hbca]; nlinarith
    · simp only [orient_self23, mul_zero, add_zero]; nlinarith
  rcases hcase with hv | ⟨u, v, o, hrot, h0, hp1, hp2⟩
  · rcases hv with hv | hv | hv
    · exact he2 x hx (hv ▸ hin)
    · exact he2 y hy (hv ▸ hin)
    · exact he2 z hz (hv ▸ hin)
  · obtain ⟨σ, hσ0, hσ1, hm⟩ := on_side h0 hp1 hp2
    have hu : u ∈ P := by rcases hrot.mem.1 with rfl | rfl | rfl <;> assumption
    have hv : v ∈ P := by rcases hrot.mem.2 with rfl | rfl | rfl <;> assumption
    have huv : u ≠ v := by
      rintro rfl; have := hrot.orient; simp at this; linarith
    exact side_not_through hP hT hg hu hv huv (hf.side_mem hrot.side) hσ0 hσ1 (hm ▸ hin)

/-- Two faces of a non-crossing set whose interiors meet have the same vertices. -/
lemma faces_vertices {P : Finset (K × K)} (hP : GenPos P) {T : Finset (Sym2 (K × K))}
    (hT : NonCross T) {x y z a b c r : K × K} (hf : Face P T x y z) (hg : Face P T a b c)
    (hr1 : InTri x y z r) (hr2 : InTri a b c r) :
    (a = x ∨ a = y ∨ a = z) ∧ (b = x ∨ b = y ∨ b = z) ∧ (c = x ∨ c = y ∨ c = z) := by
  refine ⟨?_, ?_, ?_⟩ <;> by_contra h <;> push Not at h
  · exact faces_key hP hT hf hg h.1 h.2.1 h.2.2 hr1 hr2
  · exact faces_key hP hT hf hg.rot h.1 h.2.1 h.2.2 hr1 hr2.rot
  · exact faces_key hP hT hf hg.rot.rot h.1 h.2.1 h.2.2 hr1 hr2.rot.rot

/-- From a generic point `p` inside a triangle on `P` to a point `q` of `P` outside it, the
segment crosses a side. -/
lemma exit_cross {P : Finset (K × K)} (hP : GenPos P) {x y z q p : K × K} (hx : x ∈ P)
    (hy : y ∈ P) (hz : z ∈ P) (hq : q ∈ P) (hqx : q ≠ x) (hqy : q ≠ y) (hqz : q ≠ z)
    (hqin : ¬ InTri x y z q) (hp : InTri x y z p)
    (hgen : ∀ a ∈ P, ∀ b ∈ P, a ≠ b → orient a b p ≠ 0) :
    ∃ u v, (s(u, v) = s(x, y) ∨ s(u, v) = s(y, z) ∨ s(u, v) = s(z, x)) ∧ SCross p q u v := by
  have hD := hp.ccw
  have hxy : x ≠ y := by rintro rfl; simp at hD
  have hyz : y ≠ z := by rintro rfl; simp at hD
  have hzx : z ≠ x := by rintro rfl; simp at hD
  have n1 : orient x y q ≠ 0 := hP x hx y hy q hq hxy (Ne.symm hqx) (Ne.symm hqy)
  have n2 : orient y z q ≠ 0 := hP y hy z hz q hq hyz (Ne.symm hqy) (Ne.symm hqz)
  have n3 : orient z x q ≠ 0 := hP z hz x hx q hq hzx (Ne.symm hqz) (Ne.symm hqx)
  obtain ⟨t, ht0, ht1, hcase⟩ := exit hp n1 n2 n3 hqin
  set m := lerp p q t
  have hmpq : orient p q m = 0 := orient_lerp_self _ _ _
  have novert : ∀ v ∈ P, v ≠ q → m = v → False := by
    intro v hv hvq hmv
    apply hgen v hv q hq hvq
    rw [orient_cyc, orient_swap12, ← hmv, hmpq, neg_zero]
  rcases hcase with hv | ⟨u, v, o, hrot, h0, hp1, hp2⟩
  · rcases hv with hv | hv | hv
    · exact (novert x hx hqx.symm hv).elim
    · exact (novert y hy hqy.symm hv).elim
    · exact (novert z hz hqz.symm hv).elim
  · have hu : u ∈ P := by rcases hrot.mem.1 with rfl | rfl | rfl <;> assumption
    have hv : v ∈ P := by rcases hrot.mem.2 with rfl | rfl | rfl <;> assumption
    have hqu : q ≠ u := by rcases hrot.mem.1 with rfl | rfl | rfl <;> assumption
    have hqv : q ≠ v := by rcases hrot.mem.2 with rfl | rfl | rfl <;> assumption
    have huv : u ≠ v := by
      rintro rfl; have := hrot.orient; simp at this; linarith
    have E : (1 - t) * orient u v p + t * orient u v q = 0 := by rw [← orient_lerp]; exact h0
    have hYq : orient u v q ≠ 0 := hP u hu v hv q hq huv (Ne.symm hqu) (Ne.symm hqv)
    have B := orient_bary u v o m p q
    rw [hmpq, h0, zero_mul, add_zero, mul_zero] at B
    have hgu : orient p q u ≠ 0 := by
      rw [orient_cyc]; exact hgen q hq u hu hqu
    exact ⟨u, v, hrot.side, mul_neg_of_pos_comb hp1 hp2 hgu B.symm,
      mul_neg_of_comb_zero ht0 ht1 hYq E⟩

end TwoTri
