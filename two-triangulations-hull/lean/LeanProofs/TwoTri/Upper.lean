import LeanProofs.TwoTri.Nine
import LeanProofs.TwoTri.Transfer

/-!
# Theorem 1, upper bound: `f(n) ≤ 5` for every `n ≥ 9`
-/

set_option linter.unusedSectionVars false

namespace TwoTri

/-- The induction over `ℚ`, starting from the nine-point example. -/
theorem upper_rat (n : ℕ) (hn : 9 ≤ n) :
    ∃ P : Finset (ℚ × ℚ), P.card = n ∧ GenPos P ∧ (hullEdges P).card = 5 ∧
      ∃ A B : Finset (Sym2 (ℚ × ℚ)), IsTri P A ∧ IsTri P B ∧ A ∩ B = hullEdges P ∧
        Inv P A B := by
  induction n, hn using Nat.le_induction with
  | base =>
    refine ⟨Nine.P9, Nine.card_P9, Nine.genPos_P9, by rw [Nine.hull_P9]; exact Nine.card_H9,
      Nine.A9, Nine.B9, Nine.isTri_A9, Nine.isTri_B9, ?_, Nine.inv9⟩
    rw [Nine.inter_A9_B9, Nine.hull_P9]
  | succ n _ ih =>
    obtain ⟨P, hcard, hP, hh, A, B, hA, hB, hAB, hI⟩ := ih
    obtain ⟨p, A', B', hpP, hP', hA', hB', hhull, hinter, hI'⟩ := step hP hA hB hI
    refine ⟨insert p P, by rw [Finset.card_insert_of_notMem hpP, hcard], hP',
      by rw [hhull]; exact hh, A', B', hA', hB', by rw [hinter, hAB, hhull], hI'⟩

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- **Theorem 1 (upper bound).** For every `n ≥ 9` there are `n` points in general position,
with five hull edges, and two triangulations whose common edges are exactly the hull edges.
Stated over any ordered field, in particular over `ℝ`. -/
theorem upper (n : ℕ) (hn : 9 ≤ n) :
    ∃ P : Finset (K × K), P.card = n ∧ GenPos P ∧ (hullEdges P).card = 5 ∧
      ∃ A B : Finset (Sym2 (K × K)), IsTri P A ∧ IsTri P B ∧ A ∩ B = hullEdges P := by
  obtain ⟨P, hcard, hP, hh, A, B, hA, hB, hAB, -⟩ := upper_rat n hn
  set f : ℚ →+* K := Rat.castHom K
  have hf : StrictMono f := Rat.cast_strictMono
  have inj := pmap_inj f hf
  have injS : Function.Injective (Sym2.map (pmap f)) := Sym2.map.injective inj
  refine ⟨P.image (pmap f), by rw [Finset.card_image_of_injective _ inj, hcard],
    genPos_image f hf hP, by rw [hullEdges_image f hf, Finset.card_image_of_injective _ injS, hh],
    A.image (Sym2.map (pmap f)), B.image (Sym2.map (pmap f)), isTri_image f hf hA,
    isTri_image f hf hB, ?_⟩
  rw [← Finset.image_inter_of_injOn _ _ injS.injOn, hAB, hullEdges_image f hf]

end TwoTri
