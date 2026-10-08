import LeanProofs.TwoTri.Extend

/-!
# Section 6: the minimum for a single point set

For a set `P` of `n ≥ 3` points in general position with `h` hull edges,
`min_{A,B} |A ∩ B| = 6n - 6 - 2h - C(n,2) + oct(P)`, where `oct(P)` is the least number of
segments whose removal leaves a set that splits into two non-crossing classes (equivalently,
makes the crossing graph bipartite).
-/

set_option linter.unusedSectionVars false

namespace TwoTri

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- `S` splits into two non-crossing classes. -/
def Split (S : Finset (Sym2 (K × K))) : Prop := ∃ S₁ ∈ S.powerset, NonCross S₁ ∧ NonCross (S \ S₁)

/-- The largest set of segments that splits into two non-crossing classes. -/
noncomputable def maxSplit (P : Finset (K × K)) : ℕ := by
  classical exact ((segs P).powerset.filter Split).sup Finset.card

/-- `oct(P)`: the least number of segments to remove so that the rest split. -/
noncomputable def oct (P : Finset (K × K)) : ℕ := P.card.choose 2 - maxSplit P

/-- The least number of edges shared by two triangulations of `P`. -/
def sharedSet (P : Finset (K × K)) : Set ℕ :=
  {k | ∃ A B, IsTri P A ∧ IsTri P B ∧ (A ∩ B).card = k}

lemma mem_sharedSet {P : Finset (K × K)} {k : ℕ} :
    k ∈ sharedSet P ↔ ∃ A B, IsTri P A ∧ IsTri P B ∧ (A ∩ B).card = k := Iff.rfl

noncomputable def minShared (P : Finset (K × K)) : ℕ := sInf (sharedSet P)

lemma NonCross.mono {S S' : Finset (Sym2 (K × K))} (h : NonCross S) (hS : S' ⊆ S) :
    NonCross S' := fun a ha b hb => h a (hS ha) b (hS hb)

lemma mem_splitSets {P : Finset (K × K)} {S : Finset (Sym2 (K × K))} [DecidablePred (@Split K _ _ _)] :
    S ∈ (segs P).powerset.filter Split ↔ S ⊆ segs P ∧ Split S := by
  simp

lemma le_maxSplit {P : Finset (K × K)} {S : Finset (Sym2 (K × K))} (hS : S ⊆ segs P)
    (h : Split S) : S.card ≤ maxSplit P := by
  classical
  unfold maxSplit
  convert Finset.le_sup (f := Finset.card) (Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hS, h⟩)

lemma exists_maxSplit (P : Finset (K × K)) :
    ∃ S ⊆ segs P, Split S ∧ S.card = maxSplit P := by
  classical
  have hne : ((segs P).powerset.filter Split).Nonempty :=
    ⟨∅, Finset.mem_filter.mpr ⟨Finset.empty_mem_powerset _, ∅, Finset.empty_mem_powerset _,
      fun a ha => by simp at ha, fun a ha => by simp at ha⟩⟩
  obtain ⟨S, hS, he⟩ := Finset.exists_mem_eq_sup _ hne Finset.card
  obtain ⟨hS1, hS2⟩ := Finset.mem_filter.mp hS
  refine ⟨S, Finset.mem_powerset.mp hS1, hS2, ?_⟩
  unfold maxSplit; convert he.symm

lemma maxSplit_le (P : Finset (K × K)) : maxSplit P ≤ P.card.choose 2 := by
  obtain ⟨S, hS, -, he⟩ := exists_maxSplit P
  rw [← he, ← card_segs]; exact Finset.card_le_card hS

/-- `min |A ∩ B| = |A| + |B| - max |A ∪ B|`, and the maximum union is `maxSplit P`. -/
theorem minShared_eq {P : Finset (K × K)} (hP : GenPos P) (h3 : 3 ≤ P.card) :
    minShared P + maxSplit P + 2 * (3 + (hullEdges P).card) = 6 * P.card := by
  classical
  -- every pair of triangulations
  have lower : ∀ A B, IsTri P A → IsTri P B →
      2 * (3 * P.card - 3 - (hullEdges P).card) ≤ (A ∩ B).card + maxSplit P := by
    intro A B hA hB
    have eA := edge_count hP h3 hA
    have eB := edge_count hP h3 hB
    have hU : (A ∪ B).card ≤ maxSplit P := le_maxSplit (Finset.union_subset hA.1 hB.1)
      ⟨A, Finset.mem_powerset.mpr Finset.subset_union_left, hA.2.1,
        NonCross.mono (S := B) hB.2.1 (by intro x hx; simp only [Finset.mem_sdiff, Finset.mem_union] at hx; tauto)⟩
    have := Finset.card_union_add_card_inter A B
    omega
  -- a pair attaining it
  obtain ⟨S, hS, ⟨S₁, hS₁, hn1, hn2⟩, hScard⟩ := exists_maxSplit P
  have hS₁S : S₁ ⊆ S := Finset.mem_powerset.mp hS₁
  obtain ⟨A, hA1, hA⟩ := extend (hS₁S.trans hS) hn1
  obtain ⟨B, hB1, hB⟩ := extend (Finset.sdiff_subset.trans hS) hn2
  have hUS : S ⊆ A ∪ B := by
    intro x hx
    by_cases h : x ∈ S₁
    · exact Finset.mem_union_left _ (hA1 h)
    · exact Finset.mem_union_right _ (hB1 (Finset.mem_sdiff.mpr ⟨hx, h⟩))
  have hUle : (A ∪ B).card ≤ maxSplit P := le_maxSplit (Finset.union_subset hA.1 hB.1)
    ⟨A, Finset.mem_powerset.mpr Finset.subset_union_left, hA.2.1,
      NonCross.mono (S := B) hB.2.1 (by intro x hx; simp only [Finset.mem_sdiff, Finset.mem_union] at hx; tauto)⟩
  have hUge := Finset.card_le_card hUS
  have eA := edge_count hP h3 hA
  have eB := edge_count hP h3 hB
  have hun := Finset.card_union_add_card_inter A B
  have hattain : (A ∩ B).card + maxSplit P = 2 * (3 * P.card - 3 - (hullEdges P).card) := by
    omega
  have hmin : minShared P = (A ∩ B).card := by
    unfold minShared
    apply le_antisymm (Nat.sInf_le (mem_sharedSet.mpr ⟨A, B, hA, hB, rfl⟩))
    apply le_csInf ⟨(A ∩ B).card, mem_sharedSet.mpr ⟨A, B, hA, hB, rfl⟩⟩
    intro k hk
    obtain ⟨A', B', hA', hB', rfl⟩ := mem_sharedSet.mp hk
    have := lower A' B' hA' hB'
    omega
  omega

/-- **The formula of Section 6.** -/
theorem oct_formula {P : Finset (K × K)} (hP : GenPos P) (h3 : 3 ≤ P.card) :
    (minShared P : ℤ) = 6 * P.card - 6 - 2 * (hullEdges P).card - P.card.choose 2 + oct P := by
  have h := minShared_eq hP h3
  have hle := maxSplit_le P
  unfold oct
  push_cast [hle]
  omega

/-! ### The convex pentagon -/

namespace Pentagon

def P5 : Finset (ℚ × ℚ) := {(0, 0), (4, 0), (5, 3), (2, 5), (-1, 3)}
def hull5 : Finset (Sym2 (ℚ × ℚ)) :=
  {s((0, 0), (4, 0)), s((4, 0), (5, 3)), s((5, 3), (2, 5)), s((2, 5), (-1, 3)), s((-1, 3), (0, 0))}
/-- Fan from the first vertex. -/
def A5 : Finset (Sym2 (ℚ × ℚ)) := hull5 ∪ {s((0, 0), (5, 3)), s((0, 0), (2, 5))}
/-- Fan from the second vertex. -/
def B5 : Finset (Sym2 (ℚ × ℚ)) := hull5 ∪ {s((4, 0), (2, 5)), s((4, 0), (-1, 3))}

theorem facts : P5.card = 5 ∧ GenPos P5 ∧ hullEdges P5 = hull5 ∧ IsTri P5 A5 ∧ IsTri P5 B5 ∧
    A5 ∩ B5 = hull5 := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel⟩

/-- For a convex pentagon, `oct = 1` and the formula gives `30 - 6 - 10 - 10 + 1 = 5`: two
triangulations can share only the hull. -/
theorem pentagon : minShared P5 = 5 ∧ oct P5 = 1 := by
  obtain ⟨hc, hg, hh, hA, hB, hAB⟩ := facts
  have hh5 : (hullEdges P5).card = 5 := by rw [hh]; decide +kernel
  have hmin : minShared P5 = 5 := by
    unfold minShared
    apply le_antisymm (Nat.sInf_le (mem_sharedSet.mpr ⟨A5, B5, hA, hB, by rw [hAB]; decide +kernel⟩))
    apply le_csInf ⟨(A5 ∩ B5).card, mem_sharedSet.mpr ⟨A5, B5, hA, hB, rfl⟩⟩
    intro k hk
    obtain ⟨A, B, hA', hB', rfl⟩ := mem_sharedSet.mp hk
    exact (lower hg (by rw [hc]) hA' hB').1
  refine ⟨hmin, ?_⟩
  have := oct_formula hg (by rw [hc]; norm_num)
  have hc2 : Nat.choose 5 2 = 10 := by decide
  rw [hmin, hc, hh5, hc2] at this
  omega

end Pentagon

end TwoTri
