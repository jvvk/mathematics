import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.Chebyshev

/-!
# Smallest enclosing copy (MO 458571): side data of a polygon and the identities (1)

A polygon is a cyclic list of vertices `v : Fin m → ℝ × ℝ`, taken counterclockwise. Side `i`
runs from `v i` to `v (i + 1)` (indices mod `m`). With edge `e = v (i+1) - v i` of length `L`,
the paper's side data are

* tangent `t = e / L`, outward normal `u = R_{-90°} t = (t₂, -t₁)`, so `t = R_{90°} u`;
* support number `h = v i · u` (equal to `v (i+1) · u`);
* end positions `a = v i · t`, `b = v (i+1) · t`, so `L = b - a`.

The area is the shoelace area. The identities (1) of the paper are
`∑ Lᵢ uᵢ = 0`, `∑ Lᵢ hᵢ = 2 · area` and `∑ Lᵢ bᵢ = ½ ∑ Lᵢ² = -∑ Lᵢ aᵢ`; the last one is the
telescoping of `bᵢ² - aᵢ² = |v (i+1)|² - |v i|²`.
-/

namespace Enclosing

open Finset

variable {m : ℕ} [NeZero m]

/-- Euclidean dot product on `ℝ × ℝ`. -/
def dot (x y : ℝ × ℝ) : ℝ := x.1 * y.1 + x.2 * y.2

/-- Edge vector of side `i`. -/
def edge (v : Fin m → ℝ × ℝ) (i : Fin m) : ℝ × ℝ := v (i + 1) - v i

/-- Length of side `i`. -/
noncomputable def len (v : Fin m → ℝ × ℝ) (i : Fin m) : ℝ := Real.sqrt (dot (edge v i) (edge v i))

/-- Unit tangent of side `i`. -/
noncomputable def tng (v : Fin m → ℝ × ℝ) (i : Fin m) : ℝ × ℝ :=
  ((edge v i).1 / len v i, (edge v i).2 / len v i)

/-- Outward unit normal of side `i` (for a counterclockwise polygon). -/
noncomputable def nrm (v : Fin m → ℝ × ℝ) (i : Fin m) : ℝ × ℝ :=
  ((tng v i).2, -(tng v i).1)

/-- Support number `h` of side `i`. -/
noncomputable def hsup (v : Fin m → ℝ × ℝ) (i : Fin m) : ℝ := dot (v i) (nrm v i)

/-- Position of the start of side `i` along its tangent. -/
noncomputable def aEnd (v : Fin m → ℝ × ℝ) (i : Fin m) : ℝ := dot (v i) (tng v i)

/-- Position of the end of side `i` along its tangent. -/
noncomputable def bEnd (v : Fin m → ℝ × ℝ) (i : Fin m) : ℝ := dot (v (i + 1)) (tng v i)

/-- Shoelace area. -/
noncomputable def area (v : Fin m → ℝ × ℝ) : ℝ :=
  (1 / 2) * ∑ i, ((v i).1 * (v (i + 1)).2 - (v i).2 * (v (i + 1)).1)

/-- Nondegenerate: no side of length zero. -/
def Nondeg (v : Fin m → ℝ × ℝ) : Prop := ∀ i, edge v i ≠ 0

/-- A cyclic difference sums to zero. -/
lemma sum_shift_sub (f : Fin m → ℝ) : ∑ i, (f (i + 1) - f i) = 0 := by
  rw [sum_sub_distrib, sub_eq_zero]
  exact Equiv.sum_comp (Equiv.addRight (1 : Fin m)) f

lemma len_pos (v : Fin m → ℝ × ℝ) (hv : Nondeg v) (i : Fin m) : 0 < len v i := by
  unfold len dot
  apply Real.sqrt_pos.2
  have h := hv i
  by_contra hle
  push Not at hle
  apply h
  have h1 : (edge v i).1 = 0 := by nlinarith [sq_nonneg (edge v i).1, sq_nonneg (edge v i).2]
  have h2 : (edge v i).2 = 0 := by nlinarith [sq_nonneg (edge v i).1, sq_nonneg (edge v i).2]
  exact Prod.ext h1 h2

lemma len_sq (v : Fin m → ℝ × ℝ) (i : Fin m) :
    len v i ^ 2 = (edge v i).1 ^ 2 + (edge v i).2 ^ 2 := by
  unfold len dot
  rw [Real.sq_sqrt (by nlinarith [sq_nonneg (edge v i).1, sq_nonneg (edge v i).2])]
  ring

/-- `L · t = e`, componentwise. -/
lemma len_mul_tng (v : Fin m → ℝ × ℝ) (hv : Nondeg v) (i : Fin m) :
    len v i * (tng v i).1 = (edge v i).1 ∧ len v i * (tng v i).2 = (edge v i).2 := by
  have := (len_pos v hv i).ne'
  unfold tng
  constructor <;> field_simp

/-- `L = b - a`. -/
lemma len_eq_b_sub_a (v : Fin m → ℝ × ℝ) (hv : Nondeg v) (i : Fin m) :
    len v i = bEnd v i - aEnd v i := by
  have hL := (len_pos v hv i).ne'
  have hsq := len_sq v i
  unfold bEnd aEnd dot tng
  have he1 : (v (i + 1)).1 = (v i).1 + (edge v i).1 := by simp [edge]
  have he2 : (v (i + 1)).2 = (v i).2 + (edge v i).2 := by simp [edge]
  rw [he1, he2]
  field_simp
  linear_combination hsq

/-- Both ends of a side have the same support number. -/
lemma hsup_succ (v : Fin m → ℝ × ℝ) (i : Fin m) :
    dot (v (i + 1)) (nrm v i) = hsup v i := by
  unfold hsup nrm dot tng
  have he1 : (v (i + 1)).1 = (v i).1 + (edge v i).1 := by simp [edge]
  have he2 : (v (i + 1)).2 = (v i).2 + (edge v i).2 := by simp [edge]
  rw [he1, he2]
  ring

/-- Identity (1a): `∑ Lᵢ uᵢ = 0`. -/
theorem sum_len_nrm (v : Fin m → ℝ × ℝ) (hv : Nondeg v) :
    ∑ i, len v i * (nrm v i).1 = 0 ∧ ∑ i, len v i * (nrm v i).2 = 0 := by
  constructor
  · have : ∀ i, len v i * (nrm v i).1 = (v (i + 1)).2 - (v i).2 := fun i => by
      simpa [nrm, edge] using (len_mul_tng v hv i).2
    simp_rw [this]
    exact sum_shift_sub fun i => (v i).2
  · have : ∀ i, len v i * (nrm v i).2 = -((v (i + 1)).1 - (v i).1) := fun i => by
      have := (len_mul_tng v hv i).1
      simp only [nrm, edge, Prod.fst_sub] at this ⊢
      linarith
    simp_rw [this, sum_neg_distrib]
    rw [sum_shift_sub fun i => (v i).1, neg_zero]

/-- Identity (1b): `∑ Lᵢ hᵢ = 2 · area`. -/
theorem sum_len_hsup (v : Fin m → ℝ × ℝ) (hv : Nondeg v) :
    ∑ i, len v i * hsup v i = 2 * area v := by
  unfold area
  rw [← mul_assoc, show (2 : ℝ) * (1 / 2) = 1 by norm_num, one_mul]
  refine sum_congr rfl fun i _ => ?_
  obtain ⟨h1, h2⟩ := len_mul_tng v hv i
  simp only [hsup, nrm, dot, edge, Prod.fst_sub, Prod.snd_sub] at h1 h2 ⊢
  linear_combination (v i).1 * h2 - (v i).2 * h1

/-- The telescoping step: `Lᵢ (aᵢ + bᵢ) = |v (i+1)|² - |v i|²`. -/
lemma len_mul_a_add_b (v : Fin m → ℝ × ℝ) (hv : Nondeg v) (i : Fin m) :
    len v i * (aEnd v i + bEnd v i) = dot (v (i + 1)) (v (i + 1)) - dot (v i) (v i) := by
  obtain ⟨h1, h2⟩ := len_mul_tng v hv i
  simp only [aEnd, bEnd, dot, edge, Prod.fst_sub, Prod.snd_sub] at h1 h2 ⊢
  linear_combination ((v i).1 + (v (i + 1)).1) * h1 + ((v i).2 + (v (i + 1)).2) * h2

/-- Identity (1c): `∑ Lᵢ bᵢ = ½ ∑ Lᵢ²`. -/
theorem sum_len_b (v : Fin m → ℝ × ℝ) (hv : Nondeg v) :
    ∑ i, len v i * bEnd v i = (1 / 2) * ∑ i, len v i ^ 2 := by
  have htel : ∑ i, len v i * (aEnd v i + bEnd v i) = 0 := by
    simp_rw [len_mul_a_add_b v hv]
    exact sum_shift_sub fun i => dot (v i) (v i)
  have hab : ∀ i, len v i * (aEnd v i + bEnd v i) = 2 * (len v i * bEnd v i) - len v i ^ 2 :=
    fun i => by rw [len_eq_b_sub_a v hv i]; ring
  simp_rw [hab, sum_sub_distrib, ← mul_sum] at htel
  linarith

/-- Identity (1c), other half: `∑ Lᵢ aᵢ = -½ ∑ Lᵢ²`. -/
theorem sum_len_a (v : Fin m → ℝ × ℝ) (hv : Nondeg v) :
    ∑ i, len v i * aEnd v i = -((1 / 2) * ∑ i, len v i ^ 2) := by
  have hb := sum_len_b v hv
  have : ∀ i, len v i * aEnd v i = len v i * bEnd v i - len v i ^ 2 :=
    fun i => by rw [len_eq_b_sub_a v hv i]; ring
  simp_rw [this, sum_sub_distrib, hb]
  ring

end Enclosing
