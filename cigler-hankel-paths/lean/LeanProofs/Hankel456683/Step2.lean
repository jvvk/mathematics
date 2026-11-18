import LeanProofs.Hankel456683.Walks

/-!
# Step 2: a path-count determinant

Cutting a path of length `i + j` after `i` steps gives `a_{i+j,k} = ∑_{l ≤ i} a_{i,l} W_j(l → k)`,
that is `(a_{i+j,k}) = P W` with `P = (a_{i,l})_{0 ≤ i,l < n}` lower unitriangular and
`W = (W_j(l → k))_{0 ≤ l,j < n}` (`hankel_eq_P_mul_W`). Hence `det (a_{i+j,k}) = det W`
(`det_hankel_eq_det_W`). Both hold for every weight sequence `s`.
-/

namespace Hankel456683

open Finset Matrix

variable {R : Type*} [CommRing R]

/-- `P = (a_{i,l})_{0 ≤ i,l < n}`. -/
def P (s : ℕ → R) (n : ℕ) : Matrix (Fin n) (Fin n) R := Matrix.of fun i l => walk s i 0 l

/-- `W = (W_j(l → k))_{0 ≤ l,j < n}`: rows are starting heights, columns are lengths. -/
def W (s : ℕ → R) (k n : ℕ) : Matrix (Fin n) (Fin n) R := Matrix.of fun l j => walk s j l k

theorem det_P (s : ℕ → R) (n : ℕ) : (P s n).det = 1 := by
  rw [Matrix.det_of_isLowerTriangular]
  · refine Finset.prod_eq_one fun i _ => ?_
    simpa [P] using walk_top s i 0
  · intro i l h
    simp only [OrderDual.toDual_lt_toDual] at h
    exact walk_eq_zero_of_lt s i 0 l (by simpa using h)

/-- Step 2, the factorisation `(a_{i+j,k}) = P W`. -/
theorem hankel_eq_P_mul_W (s : ℕ → R) (k n : ℕ) :
    hankel (fun m => a s m k) n = P s n * W s k n := by
  ext i j
  simp only [hankel, P, W, a, Matrix.of_apply, Matrix.mul_apply]
  rw [walk_add s i 0 j k, Fin.sum_univ_eq_sum_range (fun l => walk s i 0 l * walk s j l k)]
  refine Finset.sum_subset (fun m hm => ?_) fun m _ hm => ?_
  · simp only [mem_range] at hm ⊢; omega
  · simp only [mem_range, not_lt] at hm
    rw [walk_eq_zero_of_lt s i 0 m (by omega), zero_mul]

/-- Step 2: `det (a_{i+j,k})_{0 ≤ i,j < n} = det (W_j(l → k))_{0 ≤ l,j < n}`. -/
theorem det_hankel_eq_det_W (s : ℕ → R) (k n : ℕ) :
    (hankel (fun m => a s m k) n).det = (W s k n).det := by
  rw [hankel_eq_P_mul_W, Matrix.det_mul, det_P, one_mul]

end Hankel456683
