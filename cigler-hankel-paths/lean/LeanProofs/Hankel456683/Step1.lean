import LeanProofs.Hankel456683.Walks

/-!
# Step 1: `c` does not matter

If `g m = ∑_j C(m,j) c^(m-j) f j` (the binomial transform), then the Hankel matrix of `g` factors
as `L (f(i+j)) Lᵀ` with `L = (C(i,r) c^(i-r))` lower unitriangular (`hankel_binomial`). The
answer quotes Vandermonde, `C(i+j,t) c^(i+j-t) = ∑_{r+s=t} C(i,r) c^(i-r) C(j,s) c^(j-s)`; here the
same identity is used in operator form, `(E + c)^(i+j) = (E + c)^i (E + c)^j` for the shift `E`,
each power expanded by the binomial theorem.

With Step 1 of `Walks` (`walk_add_const`) this gives `det_hankel_add_const`: adding a constant to
every horizontal weight leaves every Hankel determinant `det (a_{i+j,k})` unchanged, for every
weight sequence `s` (the answer's parenthetical remark), and `D_indep`:
`D_{k,n}(x,c) = D_{k,n}(x,0)`.
-/

namespace Hankel456683

open Finset Matrix

variable {R : Type*} [CommRing R]

/-- The shift `(E f) m = f (m + 1)`. -/
def E : Module.End R (ℕ → R) where
  toFun f m := f (m + 1)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem E_pow_apply (t : ℕ) (f : ℕ → R) (m : ℕ) : (((E : Module.End R (ℕ → R)) ^ t) f) m =
    f (m + t) := by
  induction t generalizing m with
  | zero => rfl
  | succ t ih =>
    rw [pow_succ', Module.End.mul_apply]
    change ((E ^ t) f) (m + 1) = _
    rw [ih]
    congr 1
    omega

/-- The binomial transform of `f` with parameter `c`, read off `(E + c)^m f` at `0`. -/
theorem binomial_eq_E (f : ℕ → R) (c : R) (m p : ℕ) :
    ∑ j ∈ range (m + 1), (m.choose j : R) * c ^ (m - j) * f (p + j) =
      ((((E : Module.End R (ℕ → R)) + algebraMap R _ c) ^ m) f) p := by
  rw [pow_add_algebraMap_apply]
  simp only [E_pow_apply]

/-- The lower unitriangular matrix `L = (C(i,r) c^(i-r))_{0 ≤ i,r < n}`. -/
def L (c : R) (n : ℕ) : Matrix (Fin n) (Fin n) R :=
  Matrix.of fun i r => ((i : ℕ).choose r : R) * c ^ ((i : ℕ) - r)

theorem det_L (c : R) (n : ℕ) : (L c n).det = 1 := by
  rw [Matrix.det_of_isLowerTriangular]
  · simp [L]
  · intro i r h
    simp only [OrderDual.toDual_lt_toDual] at h
    simp [L, Nat.choose_eq_zero_of_lt (show (i : ℕ) < r from h)]

/-- A row of `L` against a vector: only `r ≤ i` contributes. -/
theorem sum_fin_choose {n i : ℕ} (hi : i < n) (c : R) (φ : ℕ → R) :
    ∑ r : Fin n, (i.choose r : R) * c ^ (i - r) * φ r =
      ∑ r ∈ range (i + 1), (i.choose r : R) * c ^ (i - r) * φ r := by
  rw [Fin.sum_univ_eq_sum_range (fun r => (i.choose r : R) * c ^ (i - r) * φ r)]
  refine (Finset.sum_subset (fun r hr => ?_) fun r _ hr => ?_).symm
  · simp only [mem_range] at hr ⊢; omega
  · simp only [mem_range, not_lt] at hr
    simp [Nat.choose_eq_zero_of_lt (show i < r by omega)]

/-- Step 1, the factorisation `(g_{i+j}) = L (f_{i+j}) Lᵀ` for the binomial transform `g` of `f`. -/
theorem hankel_binomial (f : ℕ → R) (c : R) (n : ℕ) :
    hankel (fun m => ∑ j ∈ range (m + 1), (m.choose j : R) * c ^ (m - j) * f j) n =
      L c n * hankel f n * (L c n)ᵀ := by
  ext i j
  rw [Matrix.mul_assoc, Matrix.mul_apply]
  simp only [hankel, L, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply]
  have inner : ∀ s : Fin n, ∑ r : Fin n, f (s + r) * (((j : ℕ).choose r : R) * c ^ ((j : ℕ) - r)) =
      ((((E : Module.End R (ℕ → R)) + algebraMap R _ c) ^ (j : ℕ)) f) s := fun s => by
    rw [← binomial_eq_E, ← sum_fin_choose j.isLt]
    exact Finset.sum_congr rfl fun r _ => by ring
  simp only [inner]
  rw [sum_fin_choose i.isLt c (fun s => ((((E : Module.End R (ℕ → R)) + algebraMap R _ c) ^
    (j : ℕ)) f) s)]
  have outer := binomial_eq_E ((((E : Module.End R (ℕ → R)) + algebraMap R _ c) ^ (j : ℕ)) f) c i 0
  have lhs := binomial_eq_E f c ((i : ℕ) + j) 0
  simp only [zero_add] at outer lhs
  rw [lhs, outer, ← Module.End.mul_apply, ← pow_add]

/-- Adding a constant `c` to every horizontal weight leaves `det (a_{i+j,k})` unchanged. -/
theorem det_hankel_add_const (s : ℕ → R) (c : R) (k n : ℕ) :
    (hankel (fun m => a (fun h => s h + c) m k) n).det = (hankel (fun m => a s m k) n).det := by
  simp only [a, walk_add_const]
  rw [hankel_binomial (fun m => walk s m 0 k), Matrix.det_mul, Matrix.det_mul,
    Matrix.det_transpose, det_L]
  ring

theorem ciglerS_eq (x c : R) : ciglerS x c = fun h => ciglerS x 0 h + c := by
  funext h
  unfold ciglerS
  split_ifs <;> ring

/-- `D_{k,n}(x,c)` does not depend on `c`. -/
theorem D_indep (k n : ℕ) (x c : R) : D k n x c = D k n x 0 := by
  unfold D
  rw [ciglerS_eq x c, det_hankel_add_const]

end Hankel456683
