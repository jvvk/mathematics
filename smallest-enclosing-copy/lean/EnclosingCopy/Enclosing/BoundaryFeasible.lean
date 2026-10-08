import EnclosingCopy.Enclosing.TangentSimilarity
import EnclosingCopy.Enclosing.PhysicalBoundary
import Mathlib.Analysis.Normed.Group.Bounded

/-!
# Exact finite-sample feasibility from the physical boundary observation

On any bounded copy box a fixed cutoff makes every deeper side constraint
redundant. Away from corner overlaps, the selected boundary marks therefore
decide actual sample containment exactly, rather than approximately.
-/
namespace Enclosing
open Set
variable {m : ℕ} [NeZero m] (K : Sides m)

/-- A box in the four scaled similarity coordinates. -/
def copyBox (R : ℝ) : Set Copy :=
  {z | |z.1| ≤ R ∧ |z.2.1.1| ≤ R ∧ |z.2.1.2| ≤ R ∧ |z.2.2| ≤ R}

omit [NeZero m] in
lemma isCompact_copyBox (R : ℝ) : IsCompact (copyBox R) := by
  have he : copyBox R = Icc (-R) R ×ˢ ((Icc (-R) R ×ˢ Icc (-R) R) ×ˢ Icc (-R) R) := by
    ext z; simp only [copyBox, mem_ofPred_eq, mem_prod, mem_Icc, ← abs_le, and_assoc]
  rw [he]
  exact isCompact_Icc.prod ((isCompact_Icc.prod isCompact_Icc).prod isCompact_Icc)

/-- A uniform depth cutoff exists on every bounded copy box. -/
theorem exists_boundary_feasibility_cutoff (hG : GoodSides K) (R : ℝ) :
    ∃ T > 0, ∀ x ∈ polygonRegion K, ∀ z ∈ copyBox R, ∀ i,
      z.2.2 * dot x (sideTangent (K.u i)) - Hs K z i ≤ T := by
  have hcompact := (isCompact_polygonRegion K hG).prod (isCompact_copyBox R)
  have hc (i : Fin m) : Continuous (fun p : (ℝ × ℝ) × Copy =>
      p.2.2.2 * dot p.1 (sideTangent (K.u i)) - Hs K p.2 i) := by
    unfold Hs dot sideTangent; fun_prop
  choose B hB using fun i => hcompact.exists_bound_of_continuousOn (hc i).continuousOn
  refine ⟨1 + ∑ i, |B i|, by positivity, ?_⟩
  intro x hx z hz i
  have h := hB i (x, z) ⟨hx, hz⟩
  rw [Real.norm_eq_abs] at h
  have hi : |B i| ≤ ∑ j, |B j| := Finset.single_le_sum
    (f := fun j => |B j|) (fun _ _ => abs_nonneg _) (Finset.mem_univ i)
  exact (le_abs_self _).trans (h.trans ((le_abs_self _).trans (by linarith)))

/-- The selector's mark agrees with any uniquely shallow side. -/
lemma physicalBoundaryMark_eq_tangentPointMark {T : ℝ} {n : ℕ} (_hn : 0 < n)
    {x : ℝ × ℝ} {i : Fin m} (hi : x ∈ physicalSideStrip K i (T / n))
    (hcorner : x ∉ cornerOverlap K (T / n)) :
    physicalBoundaryMark K T n x = tangentPointMark K (1 / n) i x := by
  have hunique (j : Fin m) (hji : j ≠ i) : x ∉ physicalSideStrip K j (T / n) := by
    intro hj; exact hcorner (mem_cornerOverlap_of_strips K (Ne.symm hji) hi hj)
  have hp := PoissonPP.glueWindows_eq (List.finRange m)
    (fun i => physicalSideStrip K i (T / n)) (fun i x => (i, sideMark K i n x))
    (fun _ => (0, 0, 0)) i (List.mem_finRange i) hi (fun j _ => hunique j)
  change PoissonPP.glueWindows _ _ _ _ x = _
  rw [hp]
  simp [tangentPointMark, sideMark, depthScale, sideCoords, mul_comm]

omit [NeZero m] in
/-- Above the uniform cutoff a physical point cannot violate any side constraint. -/
lemma deep_tangentPointMark_ok {T : ℝ} {n : ℕ} (hn : 0 < n) (z : Copy)
    (x : ℝ × ℝ) (i : Fin m)
    (hline : z.2.2 * dot x (sideTangent (K.u i)) - Hs K z i ≤ T)
    (hdeep : T / n < K.h i - dot x (K.u i)) :
    ¬ violates K z (tangentPointMark K (1 / n) i x) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rw [div_lt_iff₀ hn'] at hdeep
  simp only [violates, tangentPointMark, not_lt]
  have hd : (K.h i - dot x (K.u i)) / ((1 : ℝ) / n) =
      (K.h i - dot x (K.u i)) * n := by field_simp
  rw [hd]
  linarith

/-- **Exact sample containment from boundary marks.** The only exceptional
configurations are the explicitly excluded corner overlaps. -/
theorem sample_containment_iff_boundary_feasible {T : ℝ} {n k : ℕ} (hn : 0 < n)
    (y : Fin k → ℝ × ℝ) (hy : ∀ j, y j ∈ polygonRegion K)
    (hcorner : ∀ j, y j ∉ cornerOverlap K (T / n)) (z : Copy)
    (hz : 0 < 1 + (1 / (n : ℝ)) * z.1)
    (hline : ∀ j i, z.2.2 * dot (y j) (sideTangent (K.u i)) - Hs K z i ≤ T) :
    (∀ j, y j ∈ tangentCopyRegion K (1 / n) z) ↔
      Feasible K ((PoissonPP.inWindow (physicalBoundaryWindow K T n)
        (PoissonPP.config y)).map (physicalBoundaryMark K T n)) z := by
  have hq : 0 < (1 : ℝ) / n := one_div_pos.mpr (by exact_mod_cast hn)
  constructor
  · intro hcontain p hp
    obtain ⟨x, hx, rfl⟩ := Multiset.mem_map.mp hp
    have hx' : x ∈ PoissonPP.config y ∧ x ∈ physicalBoundaryWindow K T n := by
      simpa only [PoissonPP.inWindow, Multiset.mem_filter] using hx
    obtain ⟨j, rfl⟩ := (PoissonPP.mem_config y x).mp hx'.1
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx'.2
    rw [physicalBoundaryMark_eq_tangentPointMark K hn hi (hcorner j)]
    exact (mem_tangentCopyRegion_iff_model K hq hz (y j)).mp (hcontain j) i
  · intro hfeas j
    apply (mem_tangentCopyRegion_iff_model K hq hz (y j)).mpr
    intro i
    by_cases hdepth : K.h i - dot (y j) (K.u i) ≤ T / n
    · have hstrip : y j ∈ physicalSideStrip K i (T / n) :=
        ⟨hy j, sub_nonneg.mpr (hy j i), hdepth⟩
      have hxwin : y j ∈ physicalBoundaryWindow K T n := mem_iUnion.mpr ⟨i, hstrip⟩
      have hmem : physicalBoundaryMark K T n (y j) ∈
          (PoissonPP.inWindow (physicalBoundaryWindow K T n) (PoissonPP.config y)).map
            (physicalBoundaryMark K T n) := by
        apply Multiset.mem_map.mpr
        refine ⟨y j, ?_, rfl⟩
        simp only [PoissonPP.inWindow, Multiset.mem_filter]
        exact ⟨(PoissonPP.mem_config y (y j)).mpr ⟨j, rfl⟩, hxwin⟩
      have h := hfeas _ hmem
      rwa [physicalBoundaryMark_eq_tangentPointMark K hn hstrip (hcorner j)] at h
    · exact deep_tangentPointMark_ok K hn z (y j) i (hline j i) (lt_of_not_ge hdepth)

end Enclosing
