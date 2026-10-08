import LeanProofs.TwoTri.Upper
import LeanProofs.TwoTri.Cor

/-!
# Theorem 1

`f(n)` is the least number of edges shared by two triangulations of a set of `n` points in
general position in the plane. Theorem 1: `f(n) = 5` for every `n ≥ 9`, attained with a hull of
five edges whose two triangulations share only the hull.
-/

namespace TwoTri

/-- The numbers of shared edges that occur for `n` points in general position in `ℝ²`. -/
def sharedCounts (n : ℕ) : Set ℕ :=
  {k | ∃ P : Finset (ℝ × ℝ), P.card = n ∧ GenPos P ∧
    ∃ A B : Finset (Sym2 (ℝ × ℝ)), IsTri P A ∧ IsTri P B ∧ (A ∩ B).card = k}

/-- `f(n) = min_{|P| = n} min_{A,B} |A ∩ B|`. -/
noncomputable def f (n : ℕ) : ℕ := sInf (sharedCounts n)

/-- **Theorem 1.** For every `n ≥ 9` there is a set of `n` points in general position with five
hull edges and two triangulations whose only common edges are the hull edges; and `f(n) = 5`. -/
theorem theorem1 (n : ℕ) (hn : 9 ≤ n) :
    (∃ P : Finset (ℝ × ℝ), P.card = n ∧ GenPos P ∧ (hullEdges P).card = 5 ∧
      ∃ A B : Finset (Sym2 (ℝ × ℝ)), IsTri P A ∧ IsTri P B ∧ A ∩ B = hullEdges P) ∧
    f n = 5 := by
  obtain ⟨P, hcard, hP, hh, A, B, hA, hB, hAB⟩ := upper (K := ℝ) n hn
  refine ⟨⟨P, hcard, hP, hh, A, B, hA, hB, hAB⟩, ?_⟩
  have hmem : 5 ∈ sharedCounts n := ⟨P, hcard, hP, A, B, hA, hB, by rw [hAB, hh]⟩
  apply le_antisymm (Nat.sInf_le hmem)
  apply le_csInf ⟨5, hmem⟩
  rintro k ⟨Q, hQ, hgQ, A', B', hA', hB', rfl⟩
  exact (lower hgQ (by omega) hA' hB').1

end TwoTri
