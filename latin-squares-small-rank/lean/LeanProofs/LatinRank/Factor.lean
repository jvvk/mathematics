import Mathlib

/-!
# Latin squares of small rank: the orthonormal factorisation

Let `K` be a subspace of `ℝⁿ` of dimension `d` containing every column of a real `n × m` matrix `C`.
Choose an orthonormal basis `u₁, …, u_d` of `K` and put `xᵢ = (u₁ i, …, u_d i)`,
`yⱼ = (⟨u₁, cⱼ⟩, …, ⟨u_d, cⱼ⟩)`. Then
* `C i j = ⟨xᵢ, yⱼ⟩` (expand `cⱼ` in the basis),
* `∑ᵢ ‖xᵢ‖² = d` (each `u_k` has norm `1`),
* `‖yⱼ‖² = ∑ᵢ (C i j)²` (Parseval in `K`).
-/

open Module

namespace LatinRank

variable {n m : ℕ}

local notation "E" n => EuclideanSpace ℝ (Fin n)

/-- Column `j` of `C` as a vector of `ℝⁿ`. -/
noncomputable def col (C : Matrix (Fin n) (Fin m) ℝ) (j : Fin m) : E n :=
  WithLp.toLp 2 (fun i => C i j)

@[simp] lemma col_apply (C : Matrix (Fin n) (Fin m) ℝ) (j : Fin m) (i : Fin n) :
    col C j i = C i j := rfl

lemma norm_sq_col (C : Matrix (Fin n) (Fin m) ℝ) (j : Fin m) :
    ‖col C j‖ ^ 2 = ∑ i, C i j ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]; simp

theorem factor (C : Matrix (Fin n) (Fin m) ℝ) (K : Submodule ℝ (E n))
    (hK : ∀ j, col C j ∈ K) :
    ∃ (x : Fin n → E (finrank ℝ K)) (y : Fin m → E (finrank ℝ K)),
      (∀ i j, C i j = inner ℝ (x i) (y j)) ∧
      ∑ i, ‖x i‖ ^ 2 = finrank ℝ K ∧
      ∀ j, ‖y j‖ ^ 2 = ∑ i, C i j ^ 2 := by
  set b := stdOrthonormalBasis ℝ K
  refine ⟨fun i => WithLp.toLp 2 (fun k => (b k : E n) i),
    fun j => WithLp.toLp 2 (fun k => inner ℝ (b k : E n) (col C j)), ?_, ?_, ?_⟩
  · intro i j
    have h := congrArg (fun v : K => (v : E n) i) (b.sum_repr' ⟨col C j, hK j⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul, Submodule.coe_inner] at h
    rw [PiLp.inner_apply]
    simp only [RCLike.inner_apply, conj_trivial]
    rw [← col_apply C j i, ← h]
    simp [WithLp.ofLp_sum, mul_comm]
  · simp only [EuclideanSpace.norm_sq_eq, Real.norm_eq_abs, sq_abs]
    rw [Finset.sum_comm]
    have : ∀ k, ∑ i, (b k : E n) i ^ 2 = 1 := by
      intro k
      have h1 : ‖(b k : E n)‖ = 1 := b.orthonormal.1 k
      have h2 := EuclideanSpace.norm_sq_eq (b k : E n)
      rw [h1] at h2; simpa [Real.norm_eq_abs, sq_abs] using h2.symm
    simp [this]
  · intro j
    rw [← norm_sq_col]
    have h := b.sum_inner_mul_inner ⟨col C j, hK j⟩ ⟨col C j, hK j⟩
    simp only [Submodule.coe_inner] at h
    rw [EuclideanSpace.norm_sq_eq, ← real_inner_self_eq_norm_sq, ← h]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [Real.norm_eq_abs, sq]
    rw [real_inner_comm]
    exact abs_mul_abs_self _

end LatinRank
