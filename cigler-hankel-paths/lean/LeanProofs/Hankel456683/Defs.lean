import Mathlib

/-!
# Definitions for MO 456683 (Johann Cigler, Hankel determinants of path generating functions)

* `walk s n l k`: the weighted number of Motzkin paths of length `n` from height `l` to height `k`
  that never go below `0`; up and down steps have weight `1`, a horizontal step at height `h` has
  weight `s h`. It is defined by the question's own recursion on the last step,
  `walk (n+1) l k = walk n l (k-1) + s k * walk n l k + walk n l (k+1)` (the first term absent at
  `k = 0`), with `walk 0 l k = [l = k]`. The question's `a_{n,k}` is `walk s n 0 k`.
* `ciglerS x c`: the question's weights, `s_0 = c + x` and `s_l = c` for `l > 0`.
* `hankel f n = (f (i + j))_{0 ≤ i, j < n}` and `D k n x c = det (a_{i+j,k}(x,c))_{0 ≤ i,j < n}`.
* `ciglerH k n x`: the matrix `H_{k,n}(x)` exactly as the question defines it: `h_{k-m+l, m+l} = 1`
  for `0 ≤ m ≤ k`, `l ≥ 0`, `h_{l, k+i+l} = x^i` for `i ≥ 1`, `l ≥ 0`, and `0` otherwise.
* `hE k x r s`: the closed form of the entries used in the answer, on the infinite index set
  `ℕ × ℕ`: `x^(s-r-k)` above the band, `1` inside the band `|s - r| ≤ k` when `r + s ≥ k` and
  `r + s ≡ k (mod 2)`, and `0` otherwise.
* `ballot j i`: the ballot numbers, the number of `±1` paths from `0` to `i` with `j` steps that
  never go below `0` (Motzkin paths with all horizontal weights `0`).
-/

namespace Hankel456683

open Finset Matrix

variable {R : Type*} [CommRing R]

/-- Weighted Motzkin paths from height `l` to height `k` with `n` steps, never below `0`, by the
question's last-step recursion. -/
def walk (s : ℕ → R) : ℕ → ℕ → ℕ → R
  | 0, l, k => if l = k then 1 else 0
  | n + 1, l, k =>
      (if k = 0 then 0 else walk s n l (k - 1)) + s k * walk s n l k + walk s n l (k + 1)

/-- The question's `a_{n,k}` for horizontal weights `s`. -/
def a (s : ℕ → R) (n k : ℕ) : R := walk s n 0 k

/-- The question's weights: `s_0 = c + x`, `s_l = c` for `l > 0`. -/
def ciglerS (x c : R) (l : ℕ) : R := if l = 0 then c + x else c

/-- The `n × n` Hankel matrix `(f (i + j))_{0 ≤ i, j < n}`. -/
def hankel (f : ℕ → R) (n : ℕ) : Matrix (Fin n) (Fin n) R := Matrix.of fun i j => f (i + j)

/-- `D_{k,n}(x,c) = det_{0 ≤ i,j ≤ n-1} (a_{i+j,k}(x,c))`. -/
def D (k n : ℕ) (x c : R) : R := (hankel (fun m => a (ciglerS x c) m k) n).det

open scoped Classical in
/-- Cigler's `H_{k,n}(x)`, verbatim: `h_{k-m+l, m+l} = 1` for `0 ≤ m ≤ k`, `h_{l, k+i+l} = x^i` for
`i ≥ 1`, and `0` otherwise. -/
noncomputable def ciglerH (k n : ℕ) (x : R) : Matrix (Fin n) (Fin n) R := Matrix.of fun r s =>
  if ∃ m l : ℕ, m ≤ k ∧ (r : ℕ) = k - m + l ∧ (s : ℕ) = m + l then 1
  else if ∃ i l : ℕ, 1 ≤ i ∧ (r : ℕ) = l ∧ (s : ℕ) = k + i + l then x ^ ((s : ℕ) - r - k)
  else 0

/-- The closed form of the entries of the infinite matrix `H` (rows `r`, columns `s`). -/
def hE (k : ℕ) (x : R) (r s : ℕ) : R :=
  if k + r < s then x ^ (s - r - k)
  else if r ≤ s + k ∧ k ≤ r + s ∧ (r + s - k) % 2 = 0 then 1 else 0

/-- Ballot numbers `B(j, i)`: `±1` paths from `0` to `i` with `j` steps, never below `0`. -/
def ballot (j i : ℕ) : R := walk (fun _ => (0 : R)) j 0 i

end Hankel456683
