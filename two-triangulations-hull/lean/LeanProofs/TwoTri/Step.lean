import LeanProofs.TwoTri.Regen

/-!
# One step of the induction
-/

set_option linter.unusedSectionVars false

namespace TwoTri

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- The invariant carried through the induction (see `Regen.lean`). -/
def Inv (P : Finset (K × K)) (A B : Finset (Sym2 (K × K))) : Prop :=
  ∃ x y z b₁ b₂ b₃ t₁ t₂ t₃ : K × K,
    Face P A x y z ∧ Face P B b₁ b₂ b₃ ∧ Face P B t₁ t₂ t₃ ∧
    (∀ v, (v = x ∨ v = y ∨ v = z) → v ≠ b₁ ∧ v ≠ b₂ ∧ v ≠ b₃) ∧
    (t₁ ≠ x ∧ t₁ ≠ y) ∧ (t₂ ≠ x ∧ t₂ ≠ y) ∧ (t₃ ≠ x ∧ t₃ ≠ y) ∧
    (∃ w, (w = t₁ ∨ w = t₂ ∨ w = t₃) ∧ w ≠ b₁ ∧ w ≠ b₂ ∧ w ≠ b₃) ∧
    (∃ s, 0 < s ∧ s < 1 ∧ InTri b₁ b₂ b₃ (lerp x y s)) ∧
    (∃ s, 0 < s ∧ s < 1 ∧ InTri t₁ t₂ t₃ (lerp x y s))

lemma orient_lerp' (u v a b : K × K) (s : K) :
    orient u v (lerp a b s) = orient u v a + s * (orient u v b - orient u v a) := by
  rw [orient_lerp]; ring

/-- **The induction step.** From hull-disjoint-style data with the invariant, one more point
can be added keeping triangulations, hull edges, shared edges and the invariant. -/
theorem step {P : Finset (K × K)} (hP : GenPos P) {A B : Finset (Sym2 (K × K))}
    (hA : IsTri P A) (hB : IsTri P B) (hI : Inv P A B) :
    ∃ p : K × K, ∃ A' B' : Finset (Sym2 (K × K)), p ∉ P ∧ GenPos (insert p P) ∧
      IsTri (insert p P) A' ∧ IsTri (insert p P) B' ∧
      hullEdges (insert p P) = hullEdges P ∧ A' ∩ B' = A ∩ B ∧ Inv (insert p P) A' B' := by
  obtain ⟨x, y, z, b₁, b₂, b₃, t₁, t₂, t₃, hα, hβ, hT, hdisj, hT1, hT2, hT3,
    ⟨w, hw, hw1, hw2, hw3⟩, ⟨s₀, hs0, hs1, hm⟩, hTm⟩ := hI
  set m := lerp x y s₀ with hmdef
  have hD : 0 < orient x y z := hα.2.2.2.1
  obtain ⟨hb1, hb2, hb3, -⟩ := id hβ
  obtain ⟨ht1, ht2, ht3, -⟩ := id hT
  -- a point `r` inside both faces, near `m`
  obtain ⟨ε, hε, hεc, -⟩ := exists_small (Finset.univ : Finset (Fin 4)) (∅ : Finset Unit)
    ![orient b₁ b₂ m, orient b₂ b₃ m, orient b₃ b₁ m, 1]
    ![orient b₁ b₂ z - orient b₁ b₂ m, orient b₂ b₃ z - orient b₂ b₃ m,
      orient b₃ b₁ z - orient b₃ b₁ m, -1] (fun _ => (1 : K)) (fun _ => 0)
    (by intro i _; fin_cases i; exacts [hm.1, hm.2.1, hm.2.2, one_pos]) (by simp)
  have e0 := hεc 0 (by simp); have e1 := hεc 1 (by simp)
  have e2 := hεc 2 (by simp); have e3 := hεc 3 (by simp)
  simp at e0 e1 e2 e3
  set r := lerp m z ε
  have hrβ : InTri b₁ b₂ b₃ r := by
    refine ⟨?_, ?_, ?_⟩ <;> rw [orient_lerp'] <;> linarith
  have hmxy : orient x y m = 0 := orient_lerp_self _ _ _
  have hmyz : orient y z m = (1 - s₀) * orient x y z := by
    rw [hmdef, orient_lerp, ← orient_cyc]; simp
  have hmzx : orient z x m = s₀ * orient x y z := by
    rw [hmdef, orient_lerp, orient_cyc z x y, orient_cyc x y z]; simp
  have hrα : InTri x y z r := by
    refine ⟨?_, ?_, ?_⟩ <;> rw [orient_lerp]
    · rw [hmxy]; nlinarith
    · rw [hmyz]; simp only [orient_self23]; nlinarith [mul_pos (sub_pos.mpr hs1) hD]
    · rw [hmzx]; simp only [orient_self13]; nlinarith [mul_pos hs0 hD]
  -- the inserted point
  obtain ⟨p, hpα, hpβ, hgen⟩ := exists_generic (P := P) hrα hrβ
  have hpP := hα.not_mem hpα
  have hpb : ∀ b ∈ P, p ≠ b := fun b hb h => hpP (h ▸ hb)
  -- a point `q` of the open segment `xy` inside `β` and on no line from `p` to a vertex of `β`
  have nz : ∀ b ∈ P, orient p b m ≠ 0 ∨ orient p b y - orient p b x ≠ 0 := by
    intro b hb
    by_contra hc; push Not at hc
    have hx0 : orient p b x = 0 := by
      have := hc.1; rw [hmdef, orient_lerp'] at this; rw [hc.2, mul_zero, add_zero] at this
      exact this
    have hy0 : orient p b y = 0 := by linarith [hc.2]
    have := orient_collinear (hpb b hb) hx0 hy0
    linarith [hpα.1]
  obtain ⟨δ, hδ, hδc, hδg⟩ := exists_small (Finset.univ : Finset (Fin 4))
    (Finset.univ : Finset (Fin 3))
    ![orient b₁ b₂ m, orient b₂ b₃ m, orient b₃ b₁ m, 1 - s₀]
    ![orient b₁ b₂ y - orient b₁ b₂ x, orient b₂ b₃ y - orient b₂ b₃ x,
      orient b₃ b₁ y - orient b₃ b₁ x, -1]
    ![orient p b₁ m, orient p b₂ m, orient p b₃ m]
    ![orient p b₁ y - orient p b₁ x, orient p b₂ y - orient p b₂ x,
      orient p b₃ y - orient p b₃ x]
    (by intro i _; fin_cases i; exacts [hm.1, hm.2.1, hm.2.2, sub_pos.mpr hs1])
    (by intro j _; fin_cases j; exacts [nz b₁ hb1, nz b₂ hb2, nz b₃ hb3])
  have f0 := hδc 0 (by simp); have f1 := hδc 1 (by simp)
  have f2 := hδc 2 (by simp); have f3 := hδc 3 (by simp)
  have g0 := hδg 0 (by simp); have g1 := hδg 1 (by simp); have g2 := hδg 2 (by simp)
  simp at f0 f1 f2 f3 g0 g1 g2
  set s₁ := s₀ + δ
  set q := lerp x y s₁
  have hlq : ∀ u v : K × K, orient u v q =
      orient u v m + δ * (orient u v y - orient u v x) := by
    intro u v; simp only [q, s₁, hmdef, orient_lerp']; ring
  have hq : InTri b₁ b₂ b₃ q := by
    refine ⟨?_, ?_, ?_⟩ <;> rw [hlq] <;> [rw [hmdef] at f0 ⊢; rw [hmdef] at f1 ⊢;
      rw [hmdef] at f2 ⊢] <;> linarith
  have n1 : orient p b₁ q ≠ 0 := by rw [hlq]; exact g0
  have n2 : orient p b₂ q ≠ 0 := by rw [hlq]; exact g1
  have n3 : orient p b₃ q ≠ 0 := by rw [hlq]; exact g2
  have hs₁0 : 0 < s₁ := by simp only [s₁]; linarith
  have hs₁1 : s₁ < 1 := by simp only [s₁]; linarith
  -- assembling the new data
  set A' := star A p x y z
  set B' := star B p b₁ b₂ b₃
  have hAA : A ⊆ A' := Finset.subset_union_left
  have hBB : B ⊆ B' := Finset.subset_union_left
  have memA : ∀ v, (v = x ∨ v = y ∨ v = z) → s(p, v) ∈ A' := by
    rintro v (rfl | rfl | rfl) <;> simp [A', star]
  have memB : ∀ v, (v = b₁ ∨ v = b₂ ∨ v = b₃) → s(p, v) ∈ B' := by
    rintro v (rfl | rfl | rfl) <;> simp [B', star]
  have fα : Face (insert p P) A' x y p :=
    hα.piece hpα hAA (memA x (Or.inl rfl)) (memA y (Or.inr (Or.inl rfl)))
  have fT : Face (insert p P) B' t₁ t₂ t₃ := by
    refine hT.mono hBB fun hin => ?_
    obtain ⟨c1, c2, c3⟩ := faces_vertices hP hB.nonCross hβ hT hpβ hin
    rcases hw with rfl | rfl | rfl
    · rcases c1 with h | h | h <;> [exact hw1 h; exact hw2 h; exact hw3 h]
    · rcases c2 with h | h | h <;> [exact hw1 h; exact hw2 h; exact hw3 h]
    · rcases c3 with h | h | h <;> [exact hw1 h; exact hw2 h; exact hw3 h]
  have hbx : ∀ c, (c = b₁ ∨ c = b₂ ∨ c = b₃) → c ≠ x ∧ c ≠ y := by
    intro c hc
    obtain ⟨x1, x2, x3⟩ := hdisj x (Or.inl rfl)
    obtain ⟨y1, y2, y3⟩ := hdisj y (Or.inr (Or.inl rfl))
    rcases hc with rfl | rfl | rfl
    exacts [⟨Ne.symm x1, Ne.symm y1⟩, ⟨Ne.symm x2, Ne.symm y2⟩, ⟨Ne.symm x3, Ne.symm y3⟩]
  have finish : ∀ c₁ c₂, (c₁ = b₁ ∨ c₁ = b₂ ∨ c₁ = b₃) → (c₂ = b₁ ∨ c₂ = b₂ ∨ c₂ = b₃) →
      Face (insert p P) B' c₁ c₂ p → InTri c₁ c₂ p q → Inv (insert p P) A' B' := by
    intro c₁ c₂ hc₁ hc₂ hf hin
    have hpx : p ≠ x := hpb x hα.1
    have hpy : p ≠ y := hpb y hα.2.1
    refine ⟨x, y, p, t₁, t₂, t₃, c₁, c₂, p, fα, fT, hf, ?_, ?_, ?_, ?_, ?_, hTm, ?_⟩
    · rintro v (rfl | rfl | rfl)
      · exact ⟨Ne.symm hT1.1, Ne.symm hT2.1, Ne.symm hT3.1⟩
      · exact ⟨Ne.symm hT1.2, Ne.symm hT2.2, Ne.symm hT3.2⟩
      · exact ⟨hpb t₁ ht1, hpb t₂ ht2, hpb t₃ ht3⟩
    · exact hbx c₁ hc₁
    · exact hbx c₂ hc₂
    · exact ⟨hpx, hpy⟩
    · exact ⟨p, Or.inr (Or.inr rfl), hpb t₁ ht1, hpb t₂ ht2, hpb t₃ ht3⟩
    · exact ⟨s₁, hs₁0, hs₁1, hin⟩
  refine ⟨p, A', B', hpP, genPos_insert hP hpP hgen, insert_isTri hP hA hα hpα hgen,
    insert_isTri hP hB hβ hpβ hgen, hullEdges_insert hα hpα,
    star_inter hA.1 hB.1 hpP hb1 hb2 hb3 hdisj, ?_⟩
  rcases piece_of_signs hpβ hq n1 n2 n3 with hc | hc | hc
  · exact finish b₁ b₂ (Or.inl rfl) (Or.inr (Or.inl rfl))
      (hβ.piece hpβ hBB (memB b₁ (Or.inl rfl)) (memB b₂ (Or.inr (Or.inl rfl)))) hc
  · exact finish b₂ b₃ (Or.inr (Or.inl rfl)) (Or.inr (Or.inr rfl))
      (hβ.rot.piece hpβ.rot hBB (memB b₂ (Or.inr (Or.inl rfl)))
        (memB b₃ (Or.inr (Or.inr rfl)))) hc
  · exact finish b₃ b₁ (Or.inr (Or.inr rfl)) (Or.inl rfl)
      (hβ.rot.rot.piece hpβ.rot.rot hBB (memB b₃ (Or.inr (Or.inr rfl)))
        (memB b₁ (Or.inl rfl))) hc

end TwoTri
