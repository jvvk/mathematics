import EnclosingCopy.Enclosing.VertexCount
import EnclosingCopy.Poisson.Law

/-!
# Poisson side groups for the segment computation

`model_void_mask` gives the actual void probability for any selected side group.
`segment_groups_independent` proves independence of the observations on the sides
giving lower and upper bounds. `maskVoidFn_deriv` proves the exponential CDF
derivative used in the segment integral. The three-point Mecke integral is in
`SegmentCount`.
`SegmentBounds` constructs the finite-cutoff endpoints and proves the fixed-chord
probability including the zero-slope side constraints.
-/

namespace Enclosing
open MeasureTheory Set ENNReal
variable {m : ℕ} (K : Sides m)

def sideRegion (J : Finset (Fin m)) : Set (Pt m) := {x | x.1 ∈ J}

def maskedVz (J : Finset (Fin m)) (z : Copy) : Set (Pt m) := sideRegion J ∩ Vz K z

noncomputable def sideVoidArea (z : Copy) (i : Fin m) : ℝ :=
  z.2.2 * (K.b i ^ 2 - K.a i ^ 2) / 2 - (K.b i - K.a i) * Hs K z i

noncomputable def maskedVoidArea (J : Finset (Fin m)) (z : Copy) : ℝ :=
  ∑ i ∈ J, sideVoidArea K z i

lemma measurableSet_sideRegion (J : Finset (Fin m)) : MeasurableSet (sideRegion J) :=
  (measurable_of_countable (fun i : Fin m => i ∈ J)).setOf.preimage measurable_fst

lemma measurableSet_maskedVz (J : Finset (Fin m)) (z : Copy) : MeasurableSet (maskedVz K J z) :=
  (measurableSet_sideRegion J).inter (measurableSet_Vz K z)

lemma intensity_maskedVz (J : Finset (Fin m)) (T : ℝ) (z : Copy)
    (hE : Fits K z) (hT : Below K T z) :
    Λ K T (maskedVz K J z) = ENNReal.ofReal (maskedVoidArea K J z) := by
  unfold Λ
  rw [Measure.coe_finsetSum, Finset.sum_apply]
  have hterm : ∀ i : Fin m,
      ((Measure.dirac i).prod
        (volume.restrict (Icc (K.a i) (K.b i) ×ˢ Icc (0 : ℝ) T))) (maskedVz K J z) =
          if i ∈ J then ENNReal.ofReal (sideVoidArea K z i) else 0 := by
    intro i
    rw [Measure.dirac_prod,
      Measure.map_apply measurable_prodMk_left (measurableSet_maskedVz K J z)]
    by_cases hi : i ∈ J
    · rw [ite_eq_left hi]
      have he : Prod.mk i ⁻¹' maskedVz K J z =
          {p : ℝ × ℝ | p.2 < z.2.2 * p.1 - Hs K z i} := by
        ext p; simp [maskedVz, sideRegion, Vz, violates, hi]
      rw [he, Measure.restrict_apply' (measurableSet_Icc.prod measurableSet_Icc), inter_comm]
      exact volume_slice (K.hab i).le (hE i) (fun s hs => below_line K T z hT i hs)
    · rw [ite_eq_right hi]
      have he : Prod.mk i ⁻¹' maskedVz K J z = ∅ := by
        ext p; simp [maskedVz, sideRegion, hi]
      rw [he, measure_empty]
  simp_rw [hterm]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero]
  have hfilter : Finset.univ.filter (fun i : Fin m => i ∈ J) = J := by ext; simp
  rw [hfilter, maskedVoidArea, ← ENNReal.ofReal_sum_of_nonneg]
  intro i _
  exact line_area_nonneg (K.hab i).le (hE i)

/-- Actual Poisson void probability on a selected group of sides. -/
theorem model_void_mask (J : Finset (Fin m)) (T : ℝ) (z : Copy)
    (hE : Fits K z) (hT : Below K T z) :
    PoissonPP.law (Λ K T) (PoissonPP.voidEvent (maskedVz K J z)) =
      ENNReal.ofReal (Real.exp (-maskedVoidArea K J z)) := by
  rw [PoissonPP.voidEvent, PoissonPP.law_void _ (measurableSet_maskedVz K J z),
    intensity_maskedVz K J T z hE hT,
    ENNReal.toReal_ofReal]
  exact Finset.sum_nonneg fun i _ => line_area_nonneg (K.hab i).le (hE i)

noncomputable def positiveSides (t : ℝ × ℝ) : Finset (Fin m) :=
  Finset.univ.filter fun i => 0 < dot (K.u i) t

noncomputable def negativeSides (t : ℝ × ℝ) : Finset (Fin m) :=
  Finset.univ.filter fun i => dot (K.u i) t < 0

/-- The lower-bound and upper-bound side groups generate independent observations. -/
theorem segment_groups_independent (T : ℝ) (t : ℝ × ℝ) :
    ProbabilityTheory.Indep
      (MeasurableSpace.generateFrom (PoissonPP.voidFamily (sideRegion (positiveSides K t))))
      (MeasurableSpace.generateFrom (PoissonPP.voidFamily (sideRegion (negativeSides K t))))
      (PoissonPP.law (Λ K T)) := by
  apply PoissonPP.void_sigma_independent
  rw [Set.disjoint_left]
  intro x hx hy
  have hx' : x.1 ∈ positiveSides K t := hx
  have hy' : x.1 ∈ negativeSides K t := hy
  have hp : 0 < dot (K.u x.1) t := (Finset.mem_filter.mp hx').2
  have hn : dot (K.u x.1) t < 0 := (Finset.mem_filter.mp hy').2
  linarith

def chordCopy (z : Copy) (t : ℝ × ℝ) (y : ℝ) : Copy :=
  (z.1, (z.2.1.1 + y * t.1, z.2.1.2 + y * t.2), z.2.2)

lemma sideVoidArea_chord (z : Copy) (t : ℝ × ℝ) (y : ℝ) (i : Fin m) :
    sideVoidArea K (chordCopy z t y) i =
      sideVoidArea K z i - (K.b i - K.a i) * dot (K.u i) t * y := by
  simp only [sideVoidArea, chordCopy, Hs, dot]
  ring

lemma maskedVoidArea_chord (J : Finset (Fin m)) (z : Copy) (t : ℝ × ℝ) (y : ℝ) :
    maskedVoidArea K J (chordCopy z t y) = maskedVoidArea K J z -
      (∑ i ∈ J, (K.b i - K.a i) * dot (K.u i) t) * y := by
  simp only [maskedVoidArea, sideVoidArea_chord, Finset.sum_sub_distrib, Finset.sum_mul]

noncomputable def maskVoidFn (J : Finset (Fin m)) (z : Copy) (t : ℝ × ℝ) (y : ℝ) : ℝ :=
  Real.exp (-maskedVoidArea K J (chordCopy z t y))

/-- The derivative `F' = S F` used in the segment probability calculation. -/
theorem maskVoidFn_deriv (J : Finset (Fin m)) (z : Copy) (t : ℝ × ℝ) (y : ℝ) :
    HasDerivAt (maskVoidFn K J z t)
      ((∑ i ∈ J, (K.b i - K.a i) * dot (K.u i) t) * maskVoidFn K J z t y) y := by
  let S : ℝ := ∑ i ∈ J, (K.b i - K.a i) * dot (K.u i) t
  have he : maskVoidFn K J z t = fun y => Real.exp (-maskedVoidArea K J z + S * y) := by
    funext y
    unfold maskVoidFn
    rw [maskedVoidArea_chord]
    congr 1; dsimp [S]; ring
  rw [he]
  convert ((hasDerivAt_const y (-maskedVoidArea K J z)).add
    ((hasDerivAt_id y).const_mul S)).exp using 1 <;> simp [S] <;> ring

end Enclosing
