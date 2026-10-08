import LeanProofs.TwoTri.Main

/-!
# Tools for the face theory of a triangulation
-/

set_option linter.unusedSectionVars false

namespace TwoTri

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

lemma orient_lerp_mid (p a b r : K × K) (t : K) :
    orient p (lerp a b t) r = (1 - t) * orient p a r + t * orient p b r := by
  unfold orient lerp; ring

lemma orient_lerp_fst (a b q r : K × K) (t : K) :
    orient (lerp a b t) q r = (1 - t) * orient a q r + t * orient b q r := by
  unfold orient lerp; ring

/-- Moving from `lerp d e σ` towards `d`. -/
lemma lerp_lerp_start (d e : K × K) (σ t : K) :
    lerp (lerp d e σ) d t = lerp d e (σ - σ * t) := by
  unfold lerp; ext <;> simp <;> ring

lemma lerp_sub_mem {σ t : K} (h0 : 0 < σ) (h1 : σ < 1) (ht0 : 0 < t) (ht1 : t < 1) :
    (0 < σ - σ * t ∧ σ - σ * t < 1) ∧ (0 < σ + t - σ * t ∧ σ + t - σ * t < 1) := by
  refine ⟨⟨by nlinarith, by nlinarith⟩, ⟨by nlinarith, by nlinarith⟩⟩

/-- Leaving a triangle, assuming only that the target is strictly beyond some side line. -/
lemma exit' {x y z w d : K × K} (hw : InTri x y z w)
    (hout : orient x y d < 0 ∨ orient y z d < 0 ∨ orient z x d < 0) :
    ∃ t : K, 0 < t ∧ t < 1 ∧
      ((lerp w d t = x ∨ lerp w d t = y ∨ lerp w d t = z) ∨
        ∃ u v o, Rot x y z u v o ∧ orient u v (lerp w d t) = 0 ∧
          0 < orient v o (lerp w d t) ∧ 0 < orient o u (lerp w d t)) := by
  have hD := hw.ccw
  set A : Fin 3 → K := ![orient x y w, orient y z w, orient z x w]
  set B : Fin 3 → K := ![orient x y d, orient y z d, orient z x d]
  have hA : ∀ i, 0 < A i := by
    intro i; fin_cases i
    exacts [hw.1, hw.2.1, hw.2.2]
  have hB : ∃ i, B i < 0 := by
    rcases hout with h | h | h
    exacts [⟨0, h⟩, ⟨1, h⟩, ⟨2, h⟩]
  obtain ⟨t, ht0, ht1, hall, i, hi⟩ := first_root A B hA hB
  refine ⟨t, ht0, ht1, ?_⟩
  set m := lerp w d t
  have e1 : orient x y m = (1 - t) * A 0 + t * B 0 := orient_lerp _ _ _ _ _
  have e2 : orient y z m = (1 - t) * A 1 + t * B 1 := orient_lerp _ _ _ _ _
  have e3 : orient z x m = (1 - t) * A 2 + t * B 2 := orient_lerp _ _ _ _ _
  have g1 := hall 0; have g2 := hall 1; have g3 := hall 2
  rw [← e1] at g1; rw [← e2] at g2; rw [← e3] at g3
  have hDxy : orient z x y ≠ 0 := by rw [← orient_cyc, ← orient_cyc]; exact hD.ne'
  have hDyz : orient y z x ≠ 0 := by rw [← orient_cyc]; exact hD.ne'
  fin_cases i
  · replace hi : orient x y m = 0 := by rw [e1]; exact hi
    rcases g2.lt_or_eq with g2 | g2
    · rcases g3.lt_or_eq with g3 | g3
      · exact Or.inr ⟨x, y, z, Or.inl ⟨rfl, rfl, rfl⟩, hi, g2, g3⟩
      · exact Or.inl (Or.inl (eq_vertex hDxy g3.symm hi))
    · exact Or.inl (Or.inr (Or.inl (eq_vertex hD.ne' hi g2.symm)))
  · replace hi : orient y z m = 0 := by rw [e2]; exact hi
    rcases g3.lt_or_eq with g3 | g3
    · rcases g1.lt_or_eq with g1 | g1
      · exact Or.inr ⟨y, z, x, Or.inr (Or.inl ⟨rfl, rfl, rfl⟩), hi, g3, g1⟩
      · exact Or.inl (Or.inr (Or.inl (eq_vertex hD.ne' g1.symm hi)))
    · exact Or.inl (Or.inr (Or.inr (eq_vertex hDyz hi g3.symm)))
  · replace hi : orient z x m = 0 := by rw [e3]; exact hi
    rcases g1.lt_or_eq with g1 | g1
    · rcases g2.lt_or_eq with g2 | g2
      · exact Or.inr ⟨z, x, y, Or.inr (Or.inr ⟨rfl, rfl, rfl⟩), hi, g1, g2⟩
      · exact Or.inl (Or.inr (Or.inr (eq_vertex hDyz g2.symm hi)))
    · exact Or.inl (Or.inl (eq_vertex hDxy hi g1.symm))

/-- In general position, a point of `P` on the line through two points of `P` is one of them. -/
lemma GenPos.on_line {P : Finset (K × K)} (hP : GenPos P) {a b c : K × K} (ha : a ∈ P)
    (hb : b ∈ P) (hc : c ∈ P) (hab : a ≠ b) (h : orient a b c = 0) : c = a ∨ c = b := by
  by_contra hn; push Not at hn
  exact hP a ha b hb c hc hab (Ne.symm hn.1) (Ne.symm hn.2) h

/-- Two different segments of a general-position set with a common point interior to the first
cross. -/
lemma cross_of_common {P : Finset (K × K)} (hP : GenPos P) {a b c d : K × K} (ha : a ∈ P)
    (hb : b ∈ P) (hc : c ∈ P) (hd : d ∈ P) (hab : a ≠ b) (hcd : c ≠ d)
    (hne : s(a, b) ≠ s(c, d)) {t s : K} (ht0 : 0 < t) (ht1 : t < 1) (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (e : lerp a b t = lerp c d s) : SCross a b c d := by
  have E : (1 - s) * orient a b c + s * orient a b d = 0 := by
    rw [← orient_lerp, ← e, orient_lerp_self]
  have ta : lerp a b t ≠ a := fun h => ht0.ne' (lerp_inj hab (by rw [h, lerp_zero]))
  have tb : lerp a b t ≠ b := fun h => ht1.ne (lerp_inj hab (by rw [h, lerp_one]))
  have hcab : c ≠ a ∧ c ≠ b := by
    constructor <;> rintro rfl
    · simp only [orient_self13, mul_zero, zero_add] at E
      rcases mul_eq_zero.mp E with h | h
      · subst h; rw [lerp_zero] at e; exact ta e
      · rcases hP.on_line ha hb hd hab h with h' | h'
        · exact hcd h'.symm
        · exact hne (by rw [h'])
    · simp only [orient_self23, mul_zero, zero_add] at E
      rcases mul_eq_zero.mp E with h | h
      · subst h; rw [lerp_zero] at e; exact tb e
      · rcases hP.on_line ha hb hd hab h with h' | h'
        · exact hne (by rw [h', Sym2.eq_swap])
        · exact hcd h'.symm
  have hdab : d ≠ a ∧ d ≠ b := by
    constructor <;> rintro rfl
    · simp only [orient_self13, mul_zero, add_zero] at E
      rcases mul_eq_zero.mp E with h | h
      · have : s = 1 := by linarith
        subst this; rw [lerp_one] at e; exact ta e
      · rcases hP.on_line ha hb hc hab h with h' | h'
        · exact hcd h'
        · exact hne (by rw [h', Sym2.eq_swap])
    · simp only [orient_self23, mul_zero, add_zero] at E
      rcases mul_eq_zero.mp E with h | h
      · have : s = 1 := by linarith
        subst this; rw [lerp_one] at e; exact tb e
      · rcases hP.on_line ha hb hc hab h with h' | h'
        · exact hne (by rw [h'])
        · exact hcd h'
  exact scross_of_meet (hP a ha b hb c hc hab (Ne.symm hcab.1) (Ne.symm hcab.2))
    (hP a ha b hb d hd hab (Ne.symm hdab.1) (Ne.symm hdab.2))
    (hP c hc d hd a ha hcd hcab.1 hdab.1) (hP c hc d hd b hb hcd hcab.2 hdab.2)
    ht0.le ht1.le hs0 hs1 e

/-- The angularly first point, seen from `u`, of a finite set in an open half-plane at `u`. -/
lemma ang_min {S : Finset (K × K)} {u : K × K} (d : K × K) (hS : S.Nonempty)
    (hpos : ∀ r ∈ S, 0 < dotd d u r) : ∃ v ∈ S, ∀ y ∈ S, 0 ≤ orient u v y := by
  set s : K × K → K := fun r => dotd d u r
  set t : K × K → K := fun r => -d.2 * (r.1 - u.1) + d.1 * (r.2 - u.2)
  have hd2 : 0 < d.1 * d.1 + d.2 * d.2 := by
    obtain ⟨r, hr⟩ := hS
    have := hpos r hr
    by_contra hc; push Not at hc
    have h1 : d.1 = 0 := by nlinarith [mul_self_nonneg d.1, mul_self_nonneg d.2]
    have h2' : d.2 = 0 := by nlinarith [mul_self_nonneg d.1, mul_self_nonneg d.2]
    simp only [dotd, h1, h2', zero_mul, add_zero] at this; exact lt_irrefl _ this
  have key : ∀ a b, orient u a b * (d.1 * d.1 + d.2 * d.2) = s a * t b - t a * s b := by
    intro a b; simp only [s, t, dotd, orient]; ring
  obtain ⟨v, hv, hmin⟩ := S.exists_min_image (fun r => t r / s r) hS
  refine ⟨v, hv, fun y hy => ?_⟩
  have sv := hpos v hv; have sy := hpos y hy
  have h := hmin y hy
  rw [div_le_div_iff₀ sv sy] at h
  have : 0 ≤ orient u v y * (d.1 * d.1 + d.2 * d.2) := by rw [key]; linarith
  exact nonneg_of_mul_nonneg_left this hd2

/-- The half-plane left of `a → b` as a `dotd` half-plane. -/
lemma dotd_perp (a b r : K × K) :
    dotd (-(b.2 - a.2), b.1 - a.1) a r = orient a b r := by
  unfold dotd orient; ring

/-- Points just inside a triangle next to an interior point of a side. -/
lemma near_side {u v o q : K × K} (hD : 0 < orient u v o) {σ : K} (hσ0 : 0 < σ) (hσ1 : σ < 1)
    (hq : 0 < orient u v q) :
    ∃ t : K, 0 < t ∧ t < 1 ∧ InTri u v o (lerp (lerp u v σ) q t) := by
  set m := lerp u v σ
  have m1 : orient u v m = 0 := orient_lerp_self _ _ _
  have m2 : orient v o m = (1 - σ) * orient u v o := by
    rw [orient_lerp, orient_cyc u v o]; simp
  have m3 : orient o u m = σ * orient u v o := by
    rw [orient_lerp, orient_cyc o u v, orient_cyc u v o]; simp
  obtain ⟨t, ht, hc, -⟩ := exists_small (Finset.univ : Finset (Fin 3)) (∅ : Finset Unit)
    ![(1 - σ) * orient u v o, σ * orient u v o, 1]
    ![orient v o q - (1 - σ) * orient u v o, orient o u q - σ * orient u v o, -1]
    (fun _ => (1 : K)) (fun _ => 0)
    (by intro i _; fin_cases i
        · exact mul_pos (by linarith) hD
        · exact mul_pos hσ0 hD
        · exact one_pos) (by simp)
  have c0 := hc 0 (by simp); have c1 := hc 1 (by simp); have c2 := hc 2 (by simp)
  simp at c0 c1 c2
  refine ⟨t, ht, by linarith, ?_, ?_, ?_⟩ <;> rw [orient_lerp]
  · rw [m1]; nlinarith
  · rw [m2]; linarith
  · rw [m3]; linarith

/-- The crossing parameter along `a → b` of a crossing segment `cd` is determined by the line. -/
lemma param_eq {a b c d : K × K} {t : K} (h : orient c d (lerp a b t) = 0)
    (hne : orient c d a - orient c d b ≠ 0) :
    t = orient c d a / (orient c d a - orient c d b) := by
  rw [orient_lerp] at h
  field_simp; linarith

/-- A point inside a triangle is a positive combination for any affine functional. -/
lemma dotd_bary (d u p q r a : K × K) :
    orient p q r * dotd d u a =
      orient q r a * dotd d u p + orient r p a * dotd d u q + orient p q a * dotd d u r := by
  unfold orient dotd; ring

lemma dotd_lerp (d u a b : K × K) (t : K) :
    dotd d u (lerp a b t) = (1 - t) * dotd d u a + t * dotd d u b := by
  unfold dotd lerp; ring

end TwoTri
