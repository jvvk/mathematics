import LeanProofs.TwoTri.Cross

/-!
# Leaving a triangle

A segment from a point strictly inside a triangle to a point outside it leaves through a side
(or, degenerately, through a vertex). Two consequences, used for insertion and for faces:

* `through`: a segment between two points of a general-position set that passes through the
  interior of a triangle on that set, with neither endpoint inside, crosses one of its sides;
* `exit_cross`: a segment from a generic interior point to an outside point of the set crosses
  a side.
-/

set_option linter.unusedSectionVars false

namespace TwoTri

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- The first zero of finitely many affine functions that start positive, one of which ends
negative. -/
lemma first_root {ι : Type*} [Fintype ι] (A B : ι → K) (hA : ∀ i, 0 < A i)
    (hB : ∃ i, B i < 0) :
    ∃ t : K, 0 < t ∧ t < 1 ∧ (∀ i, 0 ≤ (1 - t) * A i + t * B i) ∧
      ∃ i, (1 - t) * A i + t * B i = 0 := by
  classical
  set S := Finset.univ.filter (fun i => B i < 0)
  have hS : S.Nonempty := by obtain ⟨i, hi⟩ := hB; exact ⟨i, by simp [S, hi]⟩
  set r : ι → K := fun i => A i / (A i - B i)
  have hne : (S.image r).Nonempty := hS.image r
  set t := (S.image r).min' hne
  obtain ⟨i0, hi0S, hi0⟩ := Finset.mem_image.mp ((S.image r).min'_mem hne)
  have hB0 : B i0 < 0 := (Finset.mem_filter.mp hi0S).2
  have hA0 := hA i0
  have hden : 0 < A i0 - B i0 := by linarith
  have ht : t = A i0 / (A i0 - B i0) := hi0.symm
  have htm : t * (A i0 - B i0) = A i0 := by rw [ht]; field_simp
  refine ⟨t, ?_, ?_, ?_, i0, ?_⟩
  · rw [ht]; exact div_pos hA0 hden
  · rw [ht, div_lt_one hden]; linarith
  · intro i
    have ht1 : t < 1 := by rw [ht, div_lt_one hden]; linarith
    have ht0 : 0 < t := by rw [ht]; exact div_pos hA0 hden
    by_cases hBi : B i < 0
    · have hle : t ≤ r i :=
        (S.image r).min'_le _ (Finset.mem_image.mpr ⟨i, by simp [S, hBi], rfl⟩)
      have hd : 0 < A i - B i := by linarith [hA i]
      have hr : r i * (A i - B i) = A i := by simp only [r]; field_simp
      nlinarith
    · push Not at hBi
      nlinarith [hA i]
  · linear_combination -htm

/-- `(u, v, o)` is one of the three rotations of `(x, y, z)`. -/
def Rot (x y z u v o : K × K) : Prop :=
  (u = x ∧ v = y ∧ o = z) ∨ (u = y ∧ v = z ∧ o = x) ∨ (u = z ∧ v = x ∧ o = y)

lemma Rot.orient {x y z u v o : K × K} (h : Rot x y z u v o) : orient u v o = orient x y z := by
  rcases h with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  · rfl
  · exact (orient_cyc _ _ _).symm
  · exact orient_cyc _ _ _

lemma Rot.mem {x y z u v o : K × K} (h : Rot x y z u v o) :
    (u = x ∨ u = y ∨ u = z) ∧ (v = x ∨ v = y ∨ v = z) := by
  rcases h with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;> simp

lemma Rot.side {x y z u v o : K × K} (h : Rot x y z u v o) :
    s(u, v) = s(x, y) ∨ s(u, v) = s(y, z) ∨ s(u, v) = s(z, x) := by
  rcases h with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;> simp

/-- Leaving a triangle: from `w` strictly inside `x y z` towards `d`, which is outside and on
no side line, the segment first reaches the boundary at a vertex or strictly inside a side. -/
lemma exit {x y z w d : K × K} (hw : InTri x y z w) (h1 : orient x y d ≠ 0)
    (h2 : orient y z d ≠ 0) (h3 : orient z x d ≠ 0) (hout : ¬ InTri x y z d) :
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
    by_contra hc; push Not at hc
    exact hout ⟨lt_of_le_of_ne (hc 0) (Ne.symm h1), lt_of_le_of_ne (hc 1) (Ne.symm h2),
      lt_of_le_of_ne (hc 2) (Ne.symm h3)⟩
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

lemma lerp_symm (a b : K × K) (t : K) : lerp b a (1 - t) = lerp a b t := by
  unfold lerp; ext <;> simp <;> ring

/-- A segment of a general-position set through the interior of a triangle on that set, with
neither endpoint strictly inside, crosses a side of the triangle. -/
lemma through {P : Finset (K × K)} (hP : GenPos P) {x y z c d : K × K} (hx : x ∈ P)
    (hy : y ∈ P) (hz : z ∈ P) (hc : c ∈ P) (hd : d ∈ P) (hcd : c ≠ d)
    (hcin : ¬ InTri x y z c) (hdin : ¬ InTri x y z d) {τ : K} (hτ0 : 0 < τ) (hτ1 : τ < 1)
    (hw : InTri x y z (lerp c d τ)) :
    ∃ u v, (s(u, v) = s(x, y) ∨ s(u, v) = s(y, z) ∨ s(u, v) = s(z, x)) ∧ SCross c d u v := by
  have hD := hw.ccw
  have hxy : x ≠ y := by rintro rfl; simp at hD
  have hyz : y ≠ z := by rintro rfl; simp at hD
  have hzx : z ≠ x := by rintro rfl; simp at hD
  -- the main case: `d` is not a vertex
  have main : ∀ c d : K × K, c ∈ P → d ∈ P → c ≠ d → d ≠ x → d ≠ y → d ≠ z →
      ¬ InTri x y z d → ∀ τ : K, 0 < τ → τ < 1 → InTri x y z (lerp c d τ) →
      ∃ u v, (s(u, v) = s(x, y) ∨ s(u, v) = s(y, z) ∨ s(u, v) = s(z, x)) ∧
        SCross c d u v := by
    intro c d hc hd hcd hdx hdy hdz hdin τ hτ0 hτ1 hw
    have n1 : orient x y d ≠ 0 := hP x hx y hy d hd hxy (Ne.symm hdx) (Ne.symm hdy)
    have n2 : orient y z d ≠ 0 := hP y hy z hz d hd hyz (Ne.symm hdy) (Ne.symm hdz)
    have n3 : orient z x d ≠ 0 := hP z hz x hx d hd hzx (Ne.symm hdz) (Ne.symm hdx)
    obtain ⟨t, ht0, ht1, hcase⟩ := exit hw n1 n2 n3 hdin
    have hm : lerp (lerp c d τ) d t = lerp c d (τ + t - τ * t) := lerp_lerp _ _ _ _
    set τ' := τ + t - τ * t
    have hτ'0 : 0 < τ' := by nlinarith
    have hτ'1 : τ' < 1 := by nlinarith
    rw [hm] at hcase
    set m := lerp c d τ'
    have hmcd : orient c d m = 0 := orient_lerp_self _ _ _
    have hmc : m ≠ c := by
      intro h
      have : lerp c d τ' = lerp c d 0 := by rw [lerp_zero]; exact h
      exact hτ'0.ne' (lerp_inj hcd this)
    have novert : ∀ v ∈ P, v ≠ d → m = v → False := by
      intro v hv hvd hmv
      exact hP c hc d hd v hv hcd (by rw [← hmv]; exact Ne.symm hmc) (Ne.symm hvd)
        (hmv ▸ hmcd)
    rcases hcase with hv | ⟨u, v, o, hrot, h0, hp1, hp2⟩
    · rcases hv with hv | hv | hv
      · exact (novert x hx hdx.symm hv).elim
      · exact (novert y hy hdy.symm hv).elim
      · exact (novert z hz hdz.symm hv).elim
    · have huv : orient u v o ≠ 0 := by rw [hrot.orient]; exact hD.ne'
      have hu : u ∈ P := by rcases hrot.mem.1 with rfl | rfl | rfl <;> assumption
      have hv : v ∈ P := by rcases hrot.mem.2 with rfl | rfl | rfl <;> assumption
      have hdu : d ≠ u := by rcases hrot.mem.1 with rfl | rfl | rfl <;> assumption
      have hdv : d ≠ v := by rcases hrot.mem.2 with rfl | rfl | rfl <;> assumption
      have hune : u ≠ v := by rintro rfl; simp at huv
      have E : (1 - τ') * orient u v c + τ' * orient u v d = 0 := by rw [← orient_lerp]; exact h0
      have hYd : orient u v d ≠ 0 := hP u hu v hv d hd hune (Ne.symm hdu) (Ne.symm hdv)
      have B := orient_bary u v o m c d
      rw [hmcd, h0, zero_mul, add_zero, mul_zero] at B
      have hgu : orient c d u ≠ 0 := by
        intro hgu
        rw [hgu, mul_zero, zero_add] at B
        have hgv : orient c d v = 0 := by
          rcases mul_eq_zero.mp B.symm with h | h
          · exact absurd h hp2.ne'
          · exact h
        by_cases hcu : c = u
        · subst hcu
          exact hP c hc d hd v hv hcd hune hdv hgv
        · exact hP c hc d hd u hu hcd hcu hdu hgu
      exact ⟨u, v, hrot.side, mul_neg_of_pos_comb hp1 hp2 hgu B.symm,
        mul_neg_of_comb_zero hτ'0 hτ'1 hYd E⟩
  by_cases hdv : d = x ∨ d = y ∨ d = z
  · by_cases hcv : c = x ∨ c = y ∨ c = z
    · exfalso
      obtain ⟨h1, h2, h3⟩ := hw
      rcases hcv with rfl | rfl | rfl <;> rcases hdv with rfl | rfl | rfl <;>
        simp [orient_lerp] at h1 h2 h3 hcd
    · push Not at hcv
      have hw' : InTri x y z (lerp d c (1 - τ)) := by rw [lerp_symm]; exact hw
      obtain ⟨u, v, hs, hx⟩ := main d c hd hc (Ne.symm hcd) hcv.1 hcv.2.1 hcv.2.2 hcin (1 - τ)
        (by linarith) (by linarith) hw'
      exact ⟨u, v, hs, scross_swap12.mp hx⟩
  · push Not at hdv
    exact main c d hc hd hcd hdv.1 hdv.2.1 hdv.2.2 hdin τ hτ0 hτ1 hw

end TwoTri
