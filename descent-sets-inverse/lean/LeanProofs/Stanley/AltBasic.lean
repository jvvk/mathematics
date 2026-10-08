/- Shared definitions for the Stanley alternating-permutation formalization. -/
import LeanProofs.Stanley.Count
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Analysis.Real.Pi.Bounds

namespace Stanley

namespace Alt

open Finset PowerSeries
open scoped Nat

/-! ### Definitions and named identities -/

/-- Rows of the Entringer (Seidel) triangle: `A(n+1, k+1) = A(n+1, k) + A(n, n-k)`, so row `n+1`
is the list of partial sums of row `n` reversed. -/
def row : ℕ → List ℕ
  | 0 => [1]
  | n + 1 => List.scanl (· + ·) 0 (row n).reverse

/-- Euler (zigzag) numbers `E n = A(n, n)`: `1, 1, 1, 2, 5, 16, 61, …` (OEIS A000111). -/
def E (n : ℕ) : ℕ := (row n).getD n 0

/-- `{0, 2, 4, …} ∩ {0, …, n-2}`: the 0-indexed descent set of an alternating permutation. -/
def altS (n : ℕ) : Finset ℕ := (range (n - 1)).filter Even

/-- `g(n)`: permutations `w` with `w` and `w⁻¹` both alternating (OEIS A007999). -/
def g (n : ℕ) : ℕ :=
  ((univ : Finset (Equiv.Perm (Fin n))).filter
    (fun w => descP w = altS n ∧ descP w⁻¹ = altS n)).card

/-- `u = artanh x = x + x³/3 + x⁵/5 + ⋯`. -/
noncomputable def u : PowerSeries ℝ := mk fun i => if Odd i then (1 : ℝ) / i else 0

/-- `(1 - x²)^(-1/2) = Σ C(2t, t)/4^t x^(2t)`. -/
noncomputable def s : PowerSeries ℝ :=
  mk fun i => if Even i then ((i.choose (i / 2) : ℕ) : ℝ) / 4 ^ (i / 2) else 0

/-- `c_{n,m}`: the coefficient of `xⁿ` in `uᵐ` (`m` odd) or `(1-x²)^(-1/2) uᵐ` (`m` even). -/
noncomputable def cc (n m : ℕ) : ℝ := coeff n (if Odd m then u ^ m else s * u ^ m)

/-- `a_m = E_m²/m!`. -/
noncomputable def a (m : ℕ) : ℝ := (E m : ℝ) ^ 2 / m !

/-- Stanley 2007, Theorem 3.1, coefficientwise; proved by `stanleyGF` in StanleyProof.lean. -/
def StanleyGF : Prop := ∀ n, (g n : ℝ) = ∑ m ∈ range (n + 1), a m * cc n m

/-- `σ_m = Σ_k (-1)^(k(m+1)) / (2k+1)^(m+1)`. -/
noncomputable def σ (m : ℕ) : ℝ := ∑' k : ℕ, (-1 : ℝ) ^ (k * (m + 1)) / (2 * k + 1 : ℝ) ^ (m + 1)

/-- The classical Euler-number series, proved by `eulerSeries` in EulerSeries.lean: `E_m/m! = 2 (2/π)^(m+1) σ_m` for `m ≥ 1`. -/
def EulerSeries : Prop :=
  ∀ m, 1 ≤ m → (E m : ℝ) / m ! = 2 * (2 / Real.pi) ^ (m + 1) * σ m

theorem E_values : [E 0, E 1, E 2, E 3, E 4, E 5, E 6, E 7, E 8, E 9] =
    [1, 1, 1, 2, 5, 16, 61, 272, 1385, 7936] := by decide

end Alt

end Stanley
