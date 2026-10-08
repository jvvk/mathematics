import EnclosingCopy.Enclosing.TriangleCone

/-!
# From a convex polygon to the model

A polygon in strictly convex position, listed counterclockwise, is one where every vertex not on
side `i` lies strictly on the inner side of the line of side `i` (`ConvexPos`). For `m ≥ 3` such
vertices, of area one, the side data of `Polygon.lean` form a `Sides m` (`sidesOf`) satisfying
`GoodSides` (`goodSides_of_convex`):

* the normals are unit vectors;
* they are distinct: a vertex of side `k` off side `i` is strictly inside side `i`'s line, so
  equal normals would give `h_k < h_i` and `h_i < h_k`;
* across an antiparallel pair, `h_i + h_j > 0` by the same vertex;
* consecutive normals are not parallel (the shared vertex rules out `u_{k+1} = -u_k`).

So Theorem 8 in the model holds for every such polygon (`convex_optFit_limit`), and Corollary 2
for every counterclockwise triangle of area one (`triangle_vertices_optFit_limit`).
-/

namespace Enclosing
open Finset

variable {m : ℕ} [NeZero m]

/-- Strictly convex position, counterclockwise: every vertex off side `i` lies strictly on the
inner side of the line of side `i`. -/
def ConvexPos (v : Fin m → ℝ × ℝ) : Prop :=
  ∀ i j : Fin m, j ≠ i → j ≠ i + 1 → dot (v j) (nrm v i) < hsup v i

section FinFacts

variable (hm : 3 ≤ m)
include hm

lemma fin_add_one_ne (i : Fin m) : i + 1 ≠ i := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 3 := ⟨m - 3, by omega⟩
  intro h
  have : i + 1 = i + 0 := by rw [add_zero]; exact h
  have h1 := add_left_cancel this
  rw [Fin.ext_iff, Fin.val_one, Fin.val_zero] at h1
  omega

lemma fin_add_two_ne (i : Fin m) : i + 1 + 1 ≠ i := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 3 := ⟨m - 3, by omega⟩
  intro h
  have : i + (1 + 1) = i + 0 := by rw [add_zero, ← add_assoc]; exact h
  have h2 := add_left_cancel this
  rw [Fin.ext_iff, Fin.val_add, Fin.val_one, Fin.val_zero, Nat.mod_eq_of_lt (by omega)] at h2
  omega

/-- A side `k ≠ i` has a vertex off side `i`. -/
lemma side_vertex_off {i k : Fin m} (hik : i ≠ k) :
    ∃ w, (w = k ∨ w = k + 1) ∧ w ≠ i ∧ w ≠ i + 1 := by
  by_cases hk : k = i + 1
  · refine ⟨k + 1, Or.inr rfl, ?_, fun h => hik (add_right_cancel h).symm⟩
    rw [hk]; exact fin_add_two_ne hm i
  · exact ⟨k, Or.inl rfl, Ne.symm hik, hk⟩

end FinFacts

variable {v : Fin m → ℝ × ℝ}

/-- Both vertices of side `k` have support number `h_k`. -/
lemma dot_side_vertex {k w : Fin m} (hw : w = k ∨ w = k + 1) : dot (v w) (nrm v k) = hsup v k := by
  rcases hw with h | h <;> subst h
  · rfl
  · exact hsup_succ v k

lemma nondeg_of_convex (hm : 3 ≤ m) (hv : ConvexPos v) : Nondeg v := by
  intro i he
  have h := hv i (i + 1 + 1) (fin_add_two_ne hm i)
    (fun h => fin_add_one_ne hm (i + 1) h)
  simp [hsup, nrm, tng, len, he, dot] at h

lemma nrm_unit (hv : Nondeg v) (i : Fin m) : (nrm v i).1 ^ 2 + (nrm v i).2 ^ 2 = 1 := by
  have hL := (len_pos v hv i).ne'
  have hsq := len_sq v i
  simp only [nrm, tng]
  field_simp
  linarith

/-- The side data of a convex polygon of area one. -/
noncomputable def sidesOf (v : Fin m → ℝ × ℝ) (hm : 3 ≤ m) (hv : ConvexPos v) (harea : area v = 1) :
    Sides m where
  h := hsup v
  u := nrm v
  a := aEnd v
  b := bEnd v
  hab i := by
    rw [← sub_pos, ← len_eq_b_sub_a v (nondeg_of_convex hm hv) i]
    exact len_pos v (nondeg_of_convex hm hv) i
  sum_u1 := by
    simp_rw [← len_eq_b_sub_a v (nondeg_of_convex hm hv)]
    exact (sum_len_nrm v (nondeg_of_convex hm hv)).1
  sum_u2 := by
    simp_rw [← len_eq_b_sub_a v (nondeg_of_convex hm hv)]
    exact (sum_len_nrm v (nondeg_of_convex hm hv)).2
  sum_h := by
    simp_rw [← len_eq_b_sub_a v (nondeg_of_convex hm hv)]
    rw [sum_len_hsup v (nondeg_of_convex hm hv), harea, mul_one]
  sum_sq := by
    have hnd := nondeg_of_convex hm hv
    have e : ∀ i, bEnd v i ^ 2 - aEnd v i ^ 2 = len v i * (aEnd v i + bEnd v i) := fun i => by
      rw [len_eq_b_sub_a v hnd i]; ring
    simp_rw [e, len_mul_a_add_b v hnd]
    exact sum_shift_sub fun i => dot (v i) (v i)

/-- Equal normals are impossible. -/
lemma nrm_injective (hm : 3 ≤ m) (hv : ConvexPos v) : Function.Injective (nrm v) := by
  intro i k h
  by_contra hik
  obtain ⟨w, hw, hwi, hwi1⟩ := side_vertex_off hm hik
  obtain ⟨w', hw', hwk, hwk1⟩ := side_vertex_off hm (Ne.symm hik)
  have a1 := hv i w hwi hwi1
  have a2 := hv k w' hwk hwk1
  rw [h] at a1
  rw [← h] at a2
  rw [dot_side_vertex hw] at a1
  rw [dot_side_vertex hw'] at a2
  linarith

lemma dot_neg_right (x y : ℝ × ℝ) : dot x (-y) = -dot x y := by
  simp only [dot, Prod.fst_neg, Prod.snd_neg]; ring

/-- Across an antiparallel pair the width is positive. -/
lemma width_of_convex (hm : 3 ≤ m) (hv : ConvexPos v) (i j : Fin m) (h : nrm v j = -nrm v i) :
    0 < hsup v i + hsup v j := by
  by_cases hij : i = j
  · subst hij
    have hu := nrm_unit (nondeg_of_convex hm hv) i
    have h1 : (nrm v i).1 = 0 := by
      have := congrArg Prod.fst h; simp only [Prod.fst_neg] at this; linarith
    have h2 : (nrm v i).2 = 0 := by
      have := congrArg Prod.snd h; simp only [Prod.snd_neg] at this; linarith
    rw [h1, h2] at hu; norm_num at hu
  · obtain ⟨w, hw, hwi, hwi1⟩ := side_vertex_off hm hij
    have a1 := hv i w hwi hwi1
    have a2 := dot_side_vertex (v := v) hw
    rw [h, dot_neg_right] at a2
    linarith

/-- **A convex polygon of area one satisfies `GoodSides`.** -/
theorem goodSides_of_convex (hm : 3 ≤ m) (hv : ConvexPos v) (harea : area v = 1) :
    GoodSides (sidesOf v hm hv harea) where
  unit := nrm_unit (nondeg_of_convex hm hv)
  inj := nrm_injective hm hv
  width := width_of_convex hm hv
  nondeg k := by
    refine ⟨k + 1, fun hc => ?_⟩
    have hu := nrm_unit (nondeg_of_convex hm hv)
    rcases unit_cross_zero (hu k) (hu (k + 1)) hc with h | h
    · exact fin_add_one_ne hm k (nrm_injective hm hv h)
    · have hw := width_of_convex hm hv k (k + 1) h
      have e1 : dot (v (k + 1)) (nrm v k) = hsup v k := hsup_succ v k
      have e2 : dot (v (k + 1)) (nrm v (k + 1)) = hsup v (k + 1) := rfl
      rw [h, dot_neg_right, e1] at e2
      linarith

/-- **Theorem 8 in the model for a convex polygon of area one.** -/
theorem convex_optFit_limit (hm : 3 ≤ m) (hv : ConvexPos v) (harea : area v = 1) :
    let K := sidesOf v hm hv harea
    Filter.Tendsto (fun n : ℕ => PoissonPP.law (Λ K n) {ω | OptFit K n ω}) Filter.atTop
      (nhds (spatialVertexIntegral K * coneVertexDensity K +
        ∑ p ∈ parPairs K, segDensity K p.1 p.2 * ∫⁻ v, chordWeightInf K p.1 v)) :=
  general_optFit_limit (goodSides_of_convex hm hv harea)

/-! ### Triangles -/

/-- A vertex strictly inside the line of side `i`, in coordinates. -/
lemma dot_lt_hsup {w : Fin m → ℝ × ℝ} {i j : Fin m} (hL : 0 < len w i)
    (hc : 0 < (w i - w j).1 * (edge w i).2 - (w i - w j).2 * (edge w i).1) :
    dot (w j) (nrm w i) < hsup w i := by
  rw [← sub_pos]
  have e : hsup w i - dot (w j) (nrm w i) =
      ((w i - w j).1 * (edge w i).2 - (w i - w j).2 * (edge w i).1) / len w i := by
    simp only [hsup, nrm, tng, dot, Prod.fst_sub, Prod.snd_sub]
    field_simp
    ring
  rw [e]; positivity

/-- A counterclockwise triangle of positive area is in strictly convex position. -/
lemma convexPos_triangle {w : Fin 3 → ℝ × ℝ} (harea : 0 < area w) : ConvexPos w := by
  have h2A : 0 < (w 1 - w 0).1 * (w 2 - w 0).2 - (w 1 - w 0).2 * (w 2 - w 0).1 := by
    simp only [area, Fin.sum_univ_three] at harea
    simp only [Prod.fst_sub, Prod.snd_sub]
    norm_num at harea
    nlinarith
  have hnd : Nondeg w := by
    intro i he
    have h1 := congrArg Prod.fst he
    have h2 := congrArg Prod.snd he
    simp only [Prod.fst_sub, Prod.snd_sub] at h2A
    fin_cases i <;> simp [edge] at h1 h2 <;> rw [sub_eq_zero] at h1 h2 <;>
      rw [h1, h2] at h2A <;> ring_nf at h2A <;> linarith
  intro i j hji hji1
  have hL := len_pos w hnd i
  fin_cases i <;> fin_cases j <;> simp at hji hji1 <;> refine dot_lt_hsup hL ?_ <;>
    simp [edge, Prod.fst_sub, Prod.snd_sub] at h2A ⊢ <;> nlinarith

/-- **Corollary 2 in the model for a triangle**: for vertices `w₀, w₁, w₂` counterclockwise
spanning area one, `P(E_n) → p(L₀², L₁², L₂²)` with `Lᵢ` the side lengths. -/
theorem triangle_vertices_optFit_limit {w : Fin 3 → ℝ × ℝ} (harea : area w = 1) :
    let K := sidesOf w (le_refl 3) (convexPos_triangle (by rw [harea]; norm_num)) harea
    Filter.Tendsto (fun n : ℕ => PoissonPP.law (Λ K n) {ω | OptFit K n ω}) Filter.atTop
      (nhds (ENNReal.ofReal (ptri (len w 0 ^ 2) (len w 1 ^ 2) (len w 2 ^ 2)))) := by
  intro K
  have hK : ∀ i, sideL K i = len w i := fun i =>
    (len_eq_b_sub_a w (nondeg_of_convex (le_refl 3)
      (convexPos_triangle (by rw [harea]; norm_num))) i).symm
  have h := triangle_optFit_limit (goodSides_of_convex (le_refl 3)
    (convexPos_triangle (by rw [harea]; norm_num)) harea)
  rwa [hK, hK, hK] at h

end Enclosing
