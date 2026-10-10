# Lean formalisation: an integral of hyperbolic tangents

Lean 4.34.0 with Mathlib v4.34.0. Build with `lake exe cache get && lake build LeanProofs`, then
`lake env lean CheckClaims.lean` prints each result's axioms (only `propext`, `Classical.choice`,
`Quot.sound`, or fewer). `python3 scripts/mutants.py` checks that 10 wrong variants fail.

The angles are `ang m j k = π j k / (2m)` (`x_k` in the paper), with `j` odd and coprime to `m`; `eps m j` is
`ε_m(j)`; `fac m j k = -i tan x_k` is one factor of `P_n` at the pole; cotangents are written `(tan x)⁻¹`.

| Paper | Lean (namespace `TanhResidues`) |
|---|---|
| Theorem 1: the constant `(2/m) 4^e e!² / (2e+1)!` | `const_identity` |
| Theorem 1: a factor at a root of unity is `-i tan(θ/2)` | `factor_identity` |
| Theorem 1: the pairings `x_{m-k}`, `x_{2m-k}`, `x_{m+k}` | `tan_pair`, `tan_refl`, `tan_tail`, `tan_ne_zero` |
| Theorem 1: `∏_{k<m} tan x_k = ε_m(j)`; a full period gives `1` | `prod_tan`, `period_prod`, `period_filter`, `periods` |
| Theorem 1: the product over all non-multiples `k ≤ n` of `m` | `fac_periodic`, `shift`, `filter_split`, `residue_product` |
| Corollary 4: only `ρ' = min(ρ, m-1-ρ)` matters | `cot_symm` |
| `P_n(1/q) = (-1)^n P_n(q)` | `inv_symm` |

## What is not formalised

The limits of single factors (`(1-u^k)/(1-u) → k`) are elementary. Lemma 2 is a form of Montgomery and Vaughan,
*Multiplicative Number Theory I*, Theorem 9.12 (a proof from their Theorem 9.7 is in the paper); the Mellin relation
`I_n = -2 D_n'(-1)` is from the question; the functional equation is their Corollary 10.9. All of these, and every
number in the paper, are checked numerically in `verify/`.
