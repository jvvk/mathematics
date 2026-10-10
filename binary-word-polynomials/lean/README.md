# Lean formalisation: binary words with the same characteristic polynomial

Lean 4.34.0 with Mathlib v4.34.0. Build with `lake exe cache get && lake build LeanProofs`, then
`lake env lean CheckClaims.lean` prints each result's axioms (only `propext`, `Classical.choice`,
`Quot.sound`, or fewer). `python3 scripts/mutants.py` checks that 11 wrong variants fail.

Words are `List Bool`. `T z = !![z, -1; 1, 0]`, `M t w` is the product of `T (t - wᵢ)` and `P t w` its `(0,0)` entry,
over any commutative ring; the results about cancelling a factor are in `ℤ[X]` with `t = X`.

| Paper | Lean (namespace `BlockReversal`) |
|---|---|
| The continuant recurrence `P(wcd) = (t - d) P(wc) - P(w)` | `P_snoc` (with `P_nil`, `P_single`) |
| `det M_w = 1`; concatenation and the bilinear form (1) | `det_M`, `M_append`, `M_flatten`, `P_split` |
| Lemma 1 (block reversal) | `transpose_prod`, `block_reversal` |
| Theorem 2 (for words) | `word_reversal` |
| Proposition 3 (interleaving) | `Gw_comm`, `block_aW`, `interleaving_mul`, `interleaving` |
| Proposition 4 (Theorem R) | `Gm_symm`, `sameClass_comm`, `row_flip`, `col_flip`, `Gm_u`, `theorem_R_mul`, `theorem_R` |
| Complementation `P_{w̄}(t) = (-1)ⁿ P_w(1 - t)` | `T_compl`, `M_compl`, `complement` |
| `λ ≠ 0`: `P_w` monic of degree `n`, other entries of lower degree | `M_degrees`, `P_monic`, `lam_ne_zero` |

## What is not formalised

That `P t w` equals `det(tI - H_w)` is the classical expansion of a tridiagonal determinant along its last row, which
gives the recurrence proved in `P_snoc`; it is cited, not formalised. The census (which coincidences exist up to
length 22 and which moves explain them) is a computation in `verify/`.
