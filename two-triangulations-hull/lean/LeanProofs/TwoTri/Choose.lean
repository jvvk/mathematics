import LeanProofs.TwoTri.Faces

/-!
# Choosing a small generic parameter

Finitely many affine conditions `c + t L > 0` with `c > 0` hold for all small `t > 0`, and
finitely many affine functions that are not identically zero vanish at finitely many `t`; so a
`t > 0` meeting all of them exists. This replaces the topological "a nonempty open set is not
covered by finitely many lines".
-/

set_option linter.unusedSectionVars false

namespace TwoTri

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

lemma exists_delta {ι : Type*} [DecidableEq ι] (F : Finset ι) (c L : ι → K)
    (hc : ∀ i ∈ F, 0 < c i) :
    ∃ δ : K, 0 < δ ∧ ∀ i ∈ F, ∀ t : K, 0 < t → t ≤ δ → 0 < c i + t * L i := by
  induction F using Finset.induction_on with
  | empty => exact ⟨1, one_pos, by simp⟩
  | insert i F hi ih =>
    obtain ⟨δ, hδ, h⟩ := ih (fun j hj => hc j (Finset.mem_insert_of_mem hj))
    have hci := hc i (Finset.mem_insert_self i F)
    have hpos : 0 < |L i| + 1 := by positivity
    refine ⟨min δ (c i / (|L i| + 1)), lt_min hδ (div_pos hci hpos), ?_⟩
    intro j hj t ht htle
    rcases Finset.mem_insert.mp hj with rfl | hj
    · have h1 : t ≤ c j / (|L j| + 1) := htle.trans (min_le_right _ _)
      have h2 : t * (|L j| + 1) ≤ c j := (le_div_iff₀ hpos).mp h1
      have h3 : -|L j| ≤ L j := neg_abs_le _
      nlinarith
    · exact h j hj t ht (htle.trans (min_le_left _ _))

lemma exists_small {ι κ : Type*} [DecidableEq ι] (F : Finset ι) (G : Finset κ)
    (c L : ι → K) (d M : κ → K) (hc : ∀ i ∈ F, 0 < c i) (hg : ∀ j ∈ G, d j ≠ 0 ∨ M j ≠ 0) :
    ∃ t : K, 0 < t ∧ (∀ i ∈ F, 0 < c i + t * L i) ∧ ∀ j ∈ G, d j + t * M j ≠ 0 := by
  classical
  obtain ⟨δ, hδ, h⟩ := exists_delta F c L hc
  set g : ℕ → K := fun m => δ / ((m : K) + 1)
  have ginj : Function.Injective g := by
    intro m n e
    simp only [g] at e
    have hm : (0 : K) < (m : K) + 1 := by positivity
    have hn : (0 : K) < (n : K) + 1 := by positivity
    rw [div_eq_div_iff hm.ne' hn.ne'] at e
    have : (m : K) = n := by
      have := mul_left_cancel₀ hδ.ne' e; linarith
    exact_mod_cast this
  obtain ⟨_, ⟨m, rfl⟩, hm⟩ :=
    (Set.infinite_range_of_injective ginj).exists_notMem_finset (G.image fun j => -d j / M j)
  have hpos : (0 : K) < (m : K) + 1 := by positivity
  have gpos : 0 < g m := div_pos hδ hpos
  have gle : g m ≤ δ := by
    simp only [g]; rw [div_le_iff₀ hpos]
    have : (0 : K) ≤ m := by positivity
    nlinarith
  refine ⟨g m, gpos, fun i hi => h i hi _ gpos gle, fun j hj => ?_⟩
  rcases hg j hj with hd | hM
  · by_cases hM : M j = 0
    · rw [hM, mul_zero, add_zero]; exact hd
    · intro e
      apply hm
      refine Finset.mem_image.mpr ⟨j, hj, ?_⟩
      field_simp; linarith
  · intro e
    apply hm
    refine Finset.mem_image.mpr ⟨j, hj, ?_⟩
    field_simp; linarith

end TwoTri
