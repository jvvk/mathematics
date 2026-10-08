import EnclosingCopy.Enclosing.Model
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# The limit LP: the optimality certificate of a vertex

The constraint of a point `x = (i, s, D)` at `z = (ε, C, Θ)` is `g_x(z) = ε hᵢ + C · uᵢ - Θ s + D ≥ 0`
(`gx`; it is `¬ violates` up to rewriting, `gx_nonneg_iff`). Its gradient is the row
`a_x = (hᵢ, uᵢ, -s)`. For four points with rows `A` and a positive certificate
`e₁ = ∑ λᵣ a_{xᵣ}`, `λ > 0`, at a copy `z*` where all four are tight:

* every copy `z` feasible for the four points has `ε(z) ≥ ε(z*)` (`vertex_optimal`), because
  `ε(z) - ε(z*) = ∑ λᵣ g_{xᵣ}(z)`;
* equality forces `z = z*` when `A` is invertible (`vertex_unique`).

So a feasible vertex with a positive certificate is the unique optimum of the limit LP.
-/

namespace Enclosing

open Matrix

variable {m : ℕ} (K : Sides m)

/-- The constraint function of a point. -/
def gx (z : Copy) (x : Pt m) : ℝ := Hs K z x.1 - z.2.2 * x.2.1 + x.2.2

lemma gx_nonneg_iff (z : Copy) (x : Pt m) : 0 ≤ gx K z x ↔ ¬ violates K z x := by
  unfold gx violates; constructor <;> intro h <;> [exact not_lt.2 (by linarith); linarith [not_lt.1 h]]

/-- The row `(hᵢ, uᵢ, -s)` of a point, as a vector indexed by `Fin 4`. -/
def row (x : Pt m) : Fin 4 → ℝ := ![K.h x.1, (K.u x.1).1, (K.u x.1).2, -x.2.1]

/-- A copy as a vector `(ε, C₁, C₂, Θ)`. -/
def zvec (z : Copy) : Fin 4 → ℝ := ![z.1, z.2.1.1, z.2.1.2, z.2.2]

lemma gx_eq (z : Copy) (x : Pt m) : gx K z x = row K x ⬝ᵥ zvec z + x.2.2 := by
  simp [gx, Hs, dot, row, zvec, dotProduct, Fin.sum_univ_succ]
  ring

/-- **The certificate.** `ε(z) - ε(z*) = ∑ λᵣ (g_{xᵣ}(z) - g_{xᵣ}(z*))`. -/
lemma eps_diff (x : Fin 4 → Pt m) (l : Fin 4 → ℝ)
    (hl : ∀ c, ∑ r, l r * row K (x r) c = if c = 0 then 1 else 0) (z z' : Copy) :
    z.1 - z'.1 = ∑ r, l r * (gx K z (x r) - gx K z' (x r)) := by
  simp_rw [gx_eq]
  have : ∀ r, row K (x r) ⬝ᵥ zvec z + (x r).2.2 - (row K (x r) ⬝ᵥ zvec z' + (x r).2.2)
      = ∑ c, row K (x r) c * (zvec z c - zvec z' c) := by
    intro r; simp only [dotProduct, add_sub_add_right_eq_sub]
    rw [← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl fun c _ => by ring
  simp_rw [this, Finset.mul_sum]
  rw [Finset.sum_comm]
  have : ∀ c, ∑ r, l r * (row K (x r) c * (zvec z c - zvec z' c))
      = (if c = 0 then 1 else 0) * (zvec z c - zvec z' c) := by
    intro c; rw [← hl c, Finset.sum_mul]; exact Finset.sum_congr rfl fun r _ => by ring
  simp_rw [this]
  simp [zvec]

/-- **A vertex with a positive certificate is optimal** among copies feasible for its points. -/
theorem vertex_optimal (x : Fin 4 → Pt m) (l : Fin 4 → ℝ) (hl0 : ∀ r, 0 < l r)
    (hl : ∀ c, ∑ r, l r * row K (x r) c = if c = 0 then 1 else 0) (zs : Copy)
    (htight : ∀ r, gx K zs (x r) = 0) (z : Copy) (hz : ∀ r, 0 ≤ gx K z (x r)) :
    zs.1 ≤ z.1 := by
  have := eps_diff K x l hl z zs
  simp_rw [htight, sub_zero] at this
  have : 0 ≤ z.1 - zs.1 := this ▸ Finset.sum_nonneg fun r _ => mul_nonneg (hl0 r).le (hz r)
  linarith

/-- **and the unique optimum** when the rows are independent. -/
theorem vertex_unique (x : Fin 4 → Pt m) (l : Fin 4 → ℝ) (hl0 : ∀ r, 0 < l r)
    (hl : ∀ c, ∑ r, l r * row K (x r) c = if c = 0 then 1 else 0)
    (hA : (Matrix.of fun r => row K (x r)).det ≠ 0) (zs : Copy)
    (htight : ∀ r, gx K zs (x r) = 0) (z : Copy) (hz : ∀ r, 0 ≤ gx K z (x r))
    (heq : z.1 = zs.1) : zvec z = zvec zs := by
  have hd := eps_diff K x l hl z zs
  simp_rw [htight, sub_zero, heq, sub_self] at hd
  -- all four constraints are tight at `z`
  have hzero : ∀ r, gx K z (x r) = 0 := by
    have hnn : ∀ r ∈ Finset.univ, 0 ≤ l r * gx K z (x r) := fun r _ => mul_nonneg (hl0 r).le (hz r)
    intro r
    have := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 hd.symm r (Finset.mem_univ r)
    exact (mul_eq_zero.1 this).resolve_left (hl0 r).ne'
  -- so `A (z - z*) = 0`
  have hker : (Matrix.of fun r => row K (x r)) *ᵥ (zvec z - zvec zs) = 0 := by
    funext r
    have h1 := gx_eq K z (x r)
    have h2 := gx_eq K zs (x r)
    rw [hzero r] at h1; rw [htight r] at h2
    simp only [mulVec, Matrix.of_apply, Pi.zero_apply, dotProduct_sub]
    linarith
  have := Matrix.eq_zero_of_mulVec_eq_zero hA hker
  exact sub_eq_zero.1 this

end Enclosing
