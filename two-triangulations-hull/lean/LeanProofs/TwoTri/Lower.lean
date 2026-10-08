import LeanProofs.TwoTri.Hull

/-!
# Section 2: Lemma 2 (sweep) and Corollary 3 (the lower bound)
-/

set_option linter.unusedSectionVars false

namespace TwoTri

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- No segment of `P` crosses `s`. -/
def Unavoidable (P : Finset (K × K)) (s : Sym2 (K × K)) : Prop := ∀ t ∈ segs P, ¬ Cross s t

/-- An unavoidable segment lies in every triangulation. -/
lemma Unavoidable.mem {P : Finset (K × K)} {T : Finset (Sym2 (K × K))} (hT : IsTri P T)
    {s : Sym2 (K × K)} (hs : s ∈ segs P) (hu : Unavoidable P s) : s ∈ T := by
  by_contra h
  obtain ⟨t, ht, hc⟩ := hT.2.2 s hs h
  exact hu t (hT.1 ht) hc

/-- Hull edges are unavoidable. -/
lemma hull_unavoidable {P : Finset (K × K)} {s : Sym2 (K × K)} (hs : s ∈ hullEdges P) :
    Unavoidable P s := by
  induction s using Sym2.ind with
  | _ a b =>
    obtain ⟨-, -, -, hh⟩ := mk_mem_hullEdges.mp hs
    intro t ht hc
    induction t using Sym2.ind with
    | _ c d =>
      obtain ⟨hc', hd', -⟩ := mk_mem_segs.mp ht
      have h1 := (cross_mk.mp hc).1
      have sgn : ∀ r ∈ P, (HullPos P a b → 0 ≤ orient a b r) ∧
          (HullPos P b a → orient a b r ≤ 0) := by
        intro r hr
        by_cases hra : r = a
        · subst hra; simp
        by_cases hrb : r = b
        · subst hrb; simp
        refine ⟨fun h => (h r hr hra hrb).le, fun h => ?_⟩
        have := h r hr hrb hra; rw [orient_swap12] at this; linarith
      rcases hullP_iff.mp hh with h | h
      · nlinarith [(sgn c hc').1 h, (sgn d hd').1 h]
      · nlinarith [(sgn c hc').2 h, (sgn d hd').2 h]

/-- **Lemma 2 (sweep).** Let `ℓ` be affine (for instance the signed distance to a line `m`),
with `ℓ u < ℓ r` for every other point `r` of `P` (all other points strictly on one side of
`m`, which passes through `u`), and let `q` minimise `ℓ` over `P \ {u}` (a point nearest to `m`).
Then no segment of `P` crosses `uq`. -/
theorem sweep {P : Finset (K × K)} {ℓ : K × K → K}
    (hℓ : ∀ a b t, ℓ (lerp a b t) = (1 - t) * ℓ a + t * ℓ b) {u q : K × K}
    (hside : ∀ r ∈ P, r ≠ u → ℓ u < ℓ r) (hq : q ∈ P) (hqu : q ≠ u)
    (hnear : ∀ r ∈ P, r ≠ u → ℓ q ≤ ℓ r) : Unavoidable P s(u, q) := by
  intro t ht hc
  induction t using Sym2.ind with
  | _ c d =>
    obtain ⟨hc', hd', -⟩ := mk_mem_segs.mp ht
    have hx := cross_mk.mp hc
    obtain ⟨τ, σ, -, hτ1, hσ0, hσ1, e⟩ := hx.meet
    have hcu : c ≠ u := by rintro rfl; have := hx.1; simp at this
    have hdu : d ≠ u := by rintro rfl; have := hx.1; simp at this
    have h1 := congrArg ℓ e
    rw [hℓ, hℓ] at h1
    have hu := hside q hq hqu
    have hc2 := hnear c hc' hcu
    have hd2 := hnear d hd' hdu
    nlinarith

/-- A point strictly inside a triangle is none of its vertices. -/
lemma InTri.ne {x y z w : K × K} (h : InTri x y z w) : w ≠ x ∧ w ≠ y ∧ w ≠ z := by
  refine ⟨?_, ?_, ?_⟩ <;> rintro rfl
  · have := h.2.2; simp at this
  · have := h.1; simp at this
  · have := h.2.1; simp at this

/-- A segment from a vertex to a point strictly inside a triangle on `P` is not a hull edge. -/
lemma not_hull_of_inTri {P : Finset (K × K)} (hP : GenPos P) {u a b q : K × K} (hu : u ∈ P)
    (ha : a ∈ P) (hb : b ∈ P) (hq : q ∈ P) (hin : InTri u a b q) : s(u, q) ∉ hullEdges P := by
  intro hh
  obtain ⟨-, -, hne, hh⟩ := mk_mem_hullEdges.mp hh
  obtain ⟨hqu, hqa, hqb⟩ := hin.ne
  have hD := hin.ccw
  have hua : u ≠ a := by rintro rfl; simp at hD
  have hub : u ≠ b := by rintro rfl; simp at hD
  have B := orient_bary u a b q u q
  simp only [orient_self23, mul_zero, orient_self13, zero_add] at B
  have n1 : orient u q a ≠ 0 := hP u hu q hq a ha hne hua hqa
  have neg := mul_neg_of_pos_comb hin.2.2 hin.1 n1 (by linarith)
  rcases hh with h | h
  · have := h a ha (Ne.symm hua) (Ne.symm hqa)
    have := h b hb (Ne.symm hub) (Ne.symm hqb)
    nlinarith
  · have := h a ha (Ne.symm hua) (Ne.symm hqa)
    have := h b hb (Ne.symm hub) (Ne.symm hqb)
    nlinarith

/-- **The ear lemma.** If `a` and `b` are the hull neighbours of the hull vertex `u` and the
triangle `u a b` has a point of `P` inside, then Lemma 2, applied with `m` parallel to `ab`,
gives an unavoidable segment `uq` with `q` inside `u a b`. -/
lemma ear {P : Finset (K × K)} {u a b i : K × K} (hb : b ∈ P) (hi : i ∈ P) (hua : HullPos P u a) (hbu : HullPos P b u) (hau : a ≠ u)
    (hbu' : b ≠ u) (hab : a ≠ b) (hin : InTri u a b i) :
    ∃ q ∈ P, InTri u a b q ∧ Unavoidable P s(u, q) := by
  classical
  have hD : 0 < orient u a b := hua b hb hbu' (Ne.symm hab)
  have hcyc : orient a b u = orient u a b := (orient_cyc u a b).symm
  set ℓ : K × K → K := fun r => orient a b u - orient a b r
  have hℓ : ∀ c d t, ℓ (lerp c d t) = (1 - t) * ℓ c + t * ℓ d := by
    intro c d t; simp only [ℓ, orient_lerp]; ring
  have small : ∀ r ∈ P, r ≠ u → orient a b r < orient u a b := by
    intro r hr hru
    by_cases hra : r = a
    · subst hra; simpa using hD
    by_cases hrb : r = b
    · subst hrb; simpa using hD
    have e := orient_sum u a b r
    have := hua r hr hru hra
    have := hbu r hr hrb hru
    linarith
  have hside : ∀ r ∈ P, r ≠ u → ℓ u < ℓ r := by
    intro r hr hru; simp only [ℓ, orient_self23, hcyc]; linarith [small r hr hru]
  have hiu : i ≠ u := hin.ne.1
  obtain ⟨q, hqS, hqmin⟩ := (P.erase u).exists_min_image ℓ ⟨i, Finset.mem_erase.mpr ⟨hiu, hi⟩⟩
  have hqP := Finset.mem_of_mem_erase hqS
  have hqu := Finset.ne_of_mem_erase hqS
  have hnear : ∀ r ∈ P, r ≠ u → ℓ q ≤ ℓ r := fun r hr hru =>
    hqmin r (Finset.mem_erase.mpr ⟨hru, hr⟩)
  have hqi := hnear i hi hiu
  have hab_q : 0 < orient a b q := by
    simp only [ℓ] at hqi; linarith [hin.2.1]
  have hqa : q ≠ a := by rintro rfl; simp at hab_q
  have hqb : q ≠ b := by rintro rfl; simp at hab_q
  refine ⟨q, hqP, ⟨hua q hqP hqu hqa, hab_q, hbu q hqP hqb hqu⟩, sweep hℓ hside hqP hqu hnear⟩

lemma hullPos_mem {P : Finset (K × K)} {a b : K × K} (ha : a ∈ P) (hb : b ∈ P) (hab : a ≠ b)
    (h : HullPos P a b) : s(a, b) ∈ hullEdges P :=
  mk_mem_hullEdges.mpr ⟨ha, hb, hab, hullP_iff.mpr (Or.inl h)⟩

lemma exists_other {P : Finset (K × K)} {k : ℕ} (hk : k < P.card) (S : Finset (K × K))
    (hS : S.card ≤ k) : ∃ c ∈ P, c ∉ S := by
  by_contra h; push Not at h
  have := Finset.card_le_card (show P ⊆ S from h); omega

end TwoTri
