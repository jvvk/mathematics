import LeanProofs.TwoTri.Fan

/-!
# The face on each side of an edge

An edge `ab` of a triangulation with a point of the set strictly to its left has a face `abc` on
that side, and only one.
-/

set_option linter.unusedSectionVars false

namespace TwoTri

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

theorem side_face {P : Finset (K × K)} (hP : GenPos P) {T : Finset (Sym2 (K × K))}
    (hT : IsTri P T) {a b : K × K} (ha : a ∈ P) (hb : b ∈ P) (hab : s(a, b) ∈ T)
    (hx : ∃ x ∈ P, 0 < orient a b x) : ∃ c ∈ P, Face P T a b c := by
  classical
  set W := P.filter (fun y => s(a, y) ∈ T ∧ 0 < orient a b y)
  have hW : W.Nonempty := by
    obtain ⟨y, hy, hyT, hyneg⟩ := fan hP hT ha (-(-(b.2 - a.2), b.1 - a.1)) (by
      obtain ⟨x, hx, hxp⟩ := hx
      exact ⟨x, hx, by rw [dotd_neg, dotd_perp]; linarith⟩)
    rw [dotd_neg, dotd_perp] at hyneg
    exact ⟨y, Finset.mem_filter.mpr ⟨hy, hyT, by linarith⟩⟩
  obtain ⟨c, hcW, hcmin⟩ := ang_min (S := W) (u := a) (-(b.2 - a.2), b.1 - a.1) hW
    (fun r hr => by rw [dotd_perp]; exact (Finset.mem_filter.mp hr).2.2)
  obtain ⟨hc, hacT, hD⟩ := Finset.mem_filter.mp hcW
  refine ⟨c, hc, consec hP hT ha hb hc hD hab hacT fun y hy hyT h1 h2 => ?_⟩
  have := hcmin y (Finset.mem_filter.mpr ⟨hy, hyT, h1⟩)
  rw [orient_swap23] at this; linarith

/-- The face on a given side of an edge is unique. -/
theorem face_unique {P : Finset (K × K)} (hP : GenPos P) {T : Finset (Sym2 (K × K))}
    (hT : NonCross T) {a b c c' : K × K} (hf : Face P T a b c) (hf' : Face P T a b c') :
    c' = c := by
  obtain ⟨hab, -, -⟩ := hf'.ne
  have hD := hf.2.2.2.1
  have hD' := hf'.2.2.2.1
  obtain ⟨t, ht0, ht1, hin⟩ := near_side hD (σ := 1 / 2) (by norm_num) (by norm_num) hD'
  have hin' : InTri a b c' (lerp (lerp a b (1 / 2)) c' t) := by
    have e1 : orient b c' (lerp a b (1 / 2)) = 1 / 2 * orient a b c' := by
      rw [orient_lerp, orient_self13, ← orient_cyc a b c']; ring
    have e2 : orient c' a (lerp a b (1 / 2)) = 1 / 2 * orient a b c' := by
      have h3 : orient c' a b = orient a b c' := by rw [orient_cyc a b c', orient_cyc b c' a]
      rw [orient_lerp, orient_self23, h3]; ring
    refine ⟨?_, ?_, ?_⟩ <;> rw [orient_lerp]
    · rw [orient_lerp_self]; nlinarith
    · rw [e1, orient_self23]; nlinarith
    · rw [e2, orient_self13]; nlinarith
  obtain ⟨-, -, h3⟩ := faces_vertices hP hT hf hf' hin hin'
  obtain ⟨-, hbc', hc'a⟩ := hf'.ne
  rcases h3 with h | h | h
  · exact absurd h hc'a
  · exact absurd h.symm hbc'
  · exact h

end TwoTri
