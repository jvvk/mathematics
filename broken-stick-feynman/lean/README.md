# Lean formalisation: a broken stick and a Feynman diagram

Lean 4.34.0 with Mathlib v4.34.0. Build with `lake exe cache get && lake build LeanProofs`, then
`lake env lean CheckClaims.lean` prints each result's axioms (only `propext`, `Classical.choice`,
`Quot.sound`). `python3 scripts/mutants.py` checks that 14 wrong variants fail.

The formalisation covers the algebra of Theorem 1 for the triangle (`K₃`) and the tetrahedron (`K₄`).
Edges of `K₄` are `01, 02, 03, 12, 13, 23`; vertex `0` is the origin and `g11, …, g23` are the entries of the
Gram matrix of the other three vertices.

| Paper | Lean (namespace `BrokenStick`) |
|---|---|
| The map (2) from the Gram matrix to the squared lengths | `gramMap3`, `gramMap3_apply` |
| Its determinant, so `dq = 2^(n(n-1)/2) dG` (`n = 3`: `-8`; `n = 2`: `-2`) | `det_gramMap3`, `det_gramMap2` |
| `N - n(n-1)/2 = n`, so `dℓ = 2^(-n) dG / ∏ ℓ_e` | `edges_minus_offdiag` |
| Identity (4): `Σ t_e ℓ_e² = tr(L_t G)` | `trace_identity3`, `trace_identity2` |
| `K₄` has 16 spanning trees (the three-edge sets that are not triangles) | `card_spanning_trees` |
| Matrix-tree theorem: `det L_t = Ψ(t)` | `det_lap3`, `det_lap2` |
| Duality (6): `Ψ(t) = (∏ t) U(1/t)` | `duality3`, `duality2` |
| The substitution `t = 1/(4β)`: `Ψ = 4^(-3) U(β)/∏β`, the one-variable Jacobian, the collected powers | `kirchhoff3_quarter_inv`, `schwinger_jacobian`, `inv_sqrt_quarter_inv`, `four_pow_half` |
| Homogeneity degree `-N/2` (simplex form (7)) | `homogeneity_degree` |
| `C₂ = 1/√π`, `C₃ = 4/π` | `C2_eq`, `C3_eq` |
| `C₃ Γ(3/2)^6 = π²/16`, so `p₃ = (π²/16) T` | `C3_feynman` |
| `p₂ = 1/4` from the simplex form, and from the Feynman form `T₂ = √π/4` | `p2_eq_quarter`, `p2_feynman` |

## What is not formalised

- The analytic inputs, quoted in the paper: the exponential representation of a broken stick (Devroye,
  Chapter V, Theorem 2.2), Schoenberg's criterion, the Schwinger representation (Lemma 1, proved in the paper
  by completing the square) and Siegel's matrix gamma integral.
- The change of variables and the interchange of integrals themselves (measure theory); Lean checks the
  algebra each of them needs.
- Theorem 1 for `n ≥ 4`, which the Python programs test by Monte Carlo for `n = 4`.
