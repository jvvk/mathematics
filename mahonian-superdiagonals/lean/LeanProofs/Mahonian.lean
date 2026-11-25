import LeanProofs.Mahonian.Defs
import LeanProofs.Mahonian.Truncation
import LeanProofs.Mahonian.Columns
import LeanProofs.Mahonian.Main
import LeanProofs.Mahonian.Degree
import LeanProofs.Mahonian.Examples
import LeanProofs.Mahonian.Report

/-
# The superdiagonals of the Mahonian triangle (CFS Conjecture 15)

Formalises `mahonian-superdiagonals/note/superdiagonals.tex` (namespace `Mahonian`).
Claesson, Franklín and Steingrímsson (EJC 30(4) 2023, Conjecture 15): for `i ≥ 1`,
`x^i S_{-i} = S_0 C^{-i} + P_i/(1-x)^i` with `P_i ∈ ℤ[x]` of degree `3i-2`.

Formalised:
* `Cinv_mul_Cat`: `1 - x C(x)` is the inverse of the Catalan series.
* `A_eq_trunc`, `I_split`: the truncation behind Lemma 2 (`k ≤ 2n+2`).
* `lemma2`, `c_eq_zero`, `c_sub_two`: Lemma 2 (`c_n = 0` for `n ≥ i-1`, `c_{i-2} = 1` for `i ≥ 2`);
  `I_diag`: its case `i = 0`, `I_n(n) = A(n,n)`.
* `lemma4`: Lemma 4,
  `(1-x)^{t+1} ∑_n A(n,t) x^n = f_t (1-x)^t + ∑_{s<t} f_s x (1-x)^s`.
* `main`: Theorem 1, `(1-x)^i (x^i S_{-i} - C^{-i} S_0) = P_i`, given `H3 i`.
* `natDegree_P`, `leadingCoeff_P`: `deg P_i = 3i-2`, leading coefficient `(-1)^i`, for `i ≥ 2`.
* `P_one`, `P_two`: `P_1 = -1 + 2x`, `P_2 = -1 + 4x - 4x^2 + x^3 + x^4`.

Hypothesis, not formalised: `H3 i`, Lemma 3 of the note (Lagrange inversion for Laurent series,
Gessel, JCTA 144 (2016), Theorem 2.1.1, eq. (2.1.4)), multiplied by `x^i`. Not formalised
either: the equivalence of `mahonian n`'s coefficients with inversion counts of permutations
(the standard generating function is taken as the definition).
-/
