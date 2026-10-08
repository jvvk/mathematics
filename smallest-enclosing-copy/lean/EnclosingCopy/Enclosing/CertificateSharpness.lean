import EnclosingCopy.Enclosing.VertexEvent
import EnclosingCopy.Enclosing.SegmentCount
import EnclosingCopy.Enclosing.TangentObjective

/-!
# Positive certificates control the tilt gap

Both certified vertices and parallel-side segments have a linear objective gap
controlling the tilt coordinate. This is the hypothesis needed by the exact
scale-stability theorem, and is derived here from their existing certificates.
-/
namespace Enclosing
open Matrix Set Filter Topology

lemma positive_certificate_coordinate_bound {ι : Type*} [Fintype ι]
    (l a g : ι → ℝ) (hl : ∀ i, 0 < l i) (hg : ∀ i, 0 ≤ g i) :
    |∑ i, a i * g i| ≤ (∑ i, |a i| / l i) * ∑ i, l i * g i := by
  have hsingle (i : ι) : l i * g i ≤ ∑ j, l j * g j :=
    Finset.single_le_sum (fun j _ => mul_nonneg (hl j).le (hg j)) (Finset.mem_univ i)
  calc
    _ ≤ ∑ i, |a i * g i| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i, |a i| * g i := by simp only [abs_mul, abs_of_nonneg (hg _)]
    _ ≤ ∑ i, (|a i| / l i) * ∑ j, l j * g j := by
      apply Finset.sum_le_sum
      intro i _
      have h := mul_le_mul_of_nonneg_left (hsingle i)
        (div_nonneg (abs_nonneg (a i)) (hl i).le)
      convert h using 1
      field_simp [(hl i).ne']
    _ = _ := by rw [Finset.sum_mul]

variable {m : ℕ} (K : Sides m)

/-- Finite positive certificates give a uniform linear tilt-gap bound. -/
lemma certificate_tilt_gap {k : ℕ} (x : Fin k → Pt m) (l a : Fin k → ℝ)
    (hl : ∀ r, 0 < l r) (zs : Copy) (htight : ∀ r, gx K zs (x r) = 0)
    (heps : ∀ z, z.1 - zs.1 = ∑ r, l r * (gx K z (x r) - gx K zs (x r)))
    (htilt : ∀ z, z.2.2 - zs.2.2 = ∑ r, a r * (gx K z (x r) - gx K zs (x r))) :
    ∃ D ≥ 0, ∀ z : Copy, (∀ r, 0 ≤ gx K z (x r)) →
      zs.1 ≤ z.1 ∧ |z.2.2 - zs.2.2| ≤ D * (z.1 - zs.1) := by
  refine ⟨∑ r, |a r| / l r,
    Finset.sum_nonneg (fun r _ => div_nonneg (abs_nonneg _) (hl r).le), ?_⟩
  intro z hz
  have he := heps z
  have ht := htilt z
  simp only [htight, sub_zero] at he ht
  have hn := Finset.sum_nonneg (fun r (_ : r ∈ Finset.univ) =>
    mul_nonneg (hl r).le (hz r))
  refine ⟨by linarith, ?_⟩
  rw [ht, he]
  exact positive_certificate_coordinate_bound l a (fun r => gx K z (x r)) hl hz

/-- Inverse rows recover every coordinate gap from constraint slacks. -/
lemma vertex_coordinate_gap (x : Fin 4 → Pt m) (hA : (vertexMatrix K x).det ≠ 0)
    (z zs : Copy) (c : Fin 4) :
    zvec z c - zvec zs c =
      ∑ r, (vertexMatrix K x)⁻¹ c r * (gx K z (x r) - gx K zs (x r)) := by
  have he : vertexMatrix K x *ᵥ (zvec z - zvec zs) =
      fun r => gx K z (x r) - gx K zs (x r) := by
    ext r
    simp only [Matrix.mulVec_sub, Pi.sub_apply, gx_eq]
    change row K (x r) ⬝ᵥ zvec z - row K (x r) ⬝ᵥ zvec zs = _
    ring
  have hinv := Matrix.nonsing_inv_mul (vertexMatrix K x) (isUnit_iff_ne_zero.mpr hA)
  have hh : zvec z - zvec zs =
      (vertexMatrix K x)⁻¹ *ᵥ (fun r => gx K z (x r) - gx K zs (x r)) := by
    rw [← he, Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]
  exact congrFun hh c

/-- A certified vertex satisfies the tilt-gap hypothesis without any stability premise. -/
theorem vertex_tilt_gap (x : Fin 4 → Pt m) (hA : (vertexMatrix K x).det ≠ 0)
    (hc : ∀ r, 0 < vertexCert K x r) :
    ∃ D ≥ 0, ∀ z : Copy, (∀ r, 0 ≤ gx K z (x r)) →
      (vertexCopy K x).1 ≤ z.1 ∧
      |z.2.2 - (vertexCopy K x).2.2| ≤ D * (z.1 - (vertexCopy K x).1) := by
  apply certificate_tilt_gap K x (vertexCert K x) (fun r => (vertexMatrix K x)⁻¹ 3 r)
    hc (vertexCopy K x) (vertexCopy_tight K x hA)
  · exact fun z => eps_diff K x _ (vertexCert_eq K x hA) z _
  · exact fun z => vertex_coordinate_gap K x hA z _ 3

variable {K} {k kb : Fin m}

/-- The two distinct points on the same side determine the tilt coordinate. -/
lemma segment_tilt_coordinate {x : Fin 3 → Pt m} (hx : SegGood k kb x)
    (z zs : Copy) :
    z.2.2 - zs.2.2 =
      (gx K z (x 0) - gx K zs (x 0) - (gx K z (x 1) - gx K zs (x 1))) /
        ((x 1).2.1 - (x 0).2.1) := by
  have hd : (x 1).2.1 - (x 0).2.1 ≠ 0 := (sub_pos.mpr hx.lt).ne'
  apply (eq_div_iff hd).mpr
  simp only [gx, Hs, hx.1, hx.2.1]
  ring

/-- Parallel-side segment certificates also supply the same tilt-gap bound. -/
theorem segment_tilt_gap (hP : ParPair K k kb) {x : Fin 3 → Pt m}
    (hx : SegGood k kb x) (c : ℝ) :
    ∃ D ≥ 0, ∀ z : Copy, (∀ r, 0 ≤ gx K z (x r)) →
      segVec K k kb x 0 ≤ z.1 ∧
      |z.2.2 - (segCopy K k (segVec K k kb x) c).2.2| ≤
        D * (z.1 - segVec K k kb x 0) := by
  obtain ⟨l, hl, hcert⟩ := seg_certificate hP hx
  let zs := segCopy K k (segVec K k kb x) c
  let a : Fin 3 → ℝ := ![1 / ((x 1).2.1 - (x 0).2.1),
    -(1 / ((x 1).2.1 - (x 0).2.1)), 0]
  apply certificate_tilt_gap K x l a hl zs (segCopy_tight hP hx c)
  · intro z
    have h1 := hcert z
    have h2 := hcert zs
    simp only [mul_sub]
    rw [Finset.sum_sub_distrib]
    linarith
  · intro z
    rw [segment_tilt_coordinate (K := K) hx z zs]
    simp [a, Fin.sum_univ_three]; ring

/-- A certified vertex is exactly the physical scale minimizer on every bounded
tilt window containing it, for all sufficiently large sample sizes. -/
theorem vertex_tangentScale_unique (K : Sides m) (x : Fin 4 → Pt m)
    (hA : (vertexMatrix K x).det ≠ 0) (hc : ∀ r, 0 < vertexCert K x r)
    {R : ℝ} (hR : 0 ≤ R) (ht : |(vertexCopy K x).2.2| ≤ R) :
    ∀ᶠ n : ℕ in atTop, ∀ z : Copy, (∀ r, 0 ≤ gx K z (x r)) → |z.2.2| ≤ R →
      (tangentScale (1 / n) z ≤ tangentScale (1 / n) (vertexCopy K x) ↔
        z = vertexCopy K x) := by
  obtain ⟨D, hD, hgap⟩ := vertex_tilt_gap K x hA hc
  have hf := tangentScale_optimal_face hR hD {z | ∀ r, 0 ≤ gx K z (x r)}
    (vertexCopy K x) (fun r => (vertexCopy_tight K x hA r).ge) ht
    (fun z hz => (hgap z hz).1) (fun z hz => (hgap z hz).2)
  filter_upwards [hf] with n hn z hz htz
  rw [hn z hz htz]
  constructor
  · intro he
    exact congrArg copyOfVec (vertex_unique K x (vertexCert K x) hc
      (vertexCert_eq K x hA) hA _ (vertexCopy_tight K x hA) z hz he)
  · intro he; rw [he]

end Enclosing
