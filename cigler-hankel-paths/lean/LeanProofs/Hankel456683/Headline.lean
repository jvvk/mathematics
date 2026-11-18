import LeanProofs.Hankel456683.Step1
import LeanProofs.Hankel456683.Step3

/-!
# Headline: Cigler's first conjecture (MO 456683)

For all `k, n` and all `x, c` in any commutative ring, `D_{k,n}(x,c)` does not depend on `c` and
equals `det H_{k,n}(x)`: Step 1 (`D_indep`), Step 2 (`det_hankel_eq_det_W`) and Step 3
(`det_W_eq_det_ciglerH`).

The quadratic recurrence `d_{k,n} d_{k,n-2k-2} - x² d_{k,n-1} d_{k,n-2k-1} = (1-x²) d_{k,n-k-1}²`
is not proved in the answer and is not formalised here.

The closed examples at the end are illustrations only: the question's displayed `H_{2,6}(x)` is
`ciglerH 2 6 x`, and `D_{1,3}(x,c) = x` as in the question's list.
-/

namespace Hankel456683

open Matrix

variable {R : Type*} [CommRing R]

/-- `D_{k,n}(x,c) = det H_{k,n}(x)` for all `k, n`. -/
theorem D_eq_det_ciglerH (k n : ℕ) (x c : R) : D k n x c = (ciglerH k n x).det := by
  rw [D_indep, D, det_hankel_eq_det_W, det_W_eq_det_ciglerH]

/-- The proved part of the answer: independence of `c`, and `D_{k,n}(x,c) = det H_{k,n}(x)`. -/
theorem headline (k n : ℕ) (x : R) :
    (∀ c c' : R, D k n x c = D k n x c') ∧ ∀ c : R, D k n x c = (ciglerH k n x).det :=
  ⟨fun c c' => by rw [D_indep, D_indep k n x c'], fun c => D_eq_det_ciglerH k n x c⟩

/-- The answer's remark: for every weight sequence `s`, adding a constant to all horizontal
weights leaves every Hankel determinant `det (a_{i+j,k})_{0 ≤ i,j < n}` unchanged. -/
theorem headline_any_weights (s : ℕ → R) (c : R) (k n : ℕ) :
    (hankel (fun m => a (fun h => s h + c) m k) n).det = (hankel (fun m => a s m k) n).det :=
  det_hankel_add_const s c k n

/-- Illustration: the question's displayed `H_{2,6}(x)`. -/
theorem ciglerH_two_six (x : R) : ciglerH 2 6 x = !![0, 0, 1, x, x ^ 2, x ^ 3;
    0, 1, 0, 1, x, x ^ 2;
    1, 0, 1, 0, 1, x;
    0, 1, 0, 1, 0, 1;
    0, 0, 1, 0, 1, 0;
    0, 0, 0, 1, 0, 1] := by
  rw [ciglerH_eq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Hmat, hE]

/-- Illustration: `D_{1,3}(x,c) = x`, the fourth entry of the question's list for `k = 1`. -/
theorem D_one_three (x c : R) : D 1 3 x c = x := by
  rw [D_eq_det_ciglerH, ciglerH_eq, Matrix.det_fin_three]
  simp [Hmat, hE]

end Hankel456683
