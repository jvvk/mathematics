# Lean proof sources

Lean 4.34.0; Mathlib is pinned by lake-manifest.json to
5ed2965256430c3649e86755f9576b54eca72435 (v4.34.0).
SOURCE-SNAPSHOT.json records the development commit and the hash of every file. Build caches are excluded.

    lake exe cache get
    lake build LeanProofs
    lake env lean CheckClaims.lean
    python3 scripts/mutants.py

The first command fetches the pinned Mathlib cache, the second compiles the proofs, the third prints the
statements and axioms of the headline results, and the last runs the mutation tests: each plants one wrong
definition, hypothesis or constant and checks that the file no longer compiles.

**Weil's bound.** `WeilBound p` states `‖K u v‖ ≤ 2 √p` for the Kloosterman sums `K u v` with `u, v ≠ 0`
(A. Weil, 1948). It is not in Mathlib and is not proved here: every theorem that needs it takes it as an
explicit hypothesis (`WeilBound p`, or `∀ p, WeilBound p` for the limit). No axiom is added.

| Paper | Lean (namespace `InversePairs`) |
|---|---|
| Kloosterman sums, Weil's bound (hypothesis) | `Rect.lean`: `ψ`, `K`, `WeilBound` |
| `K(0,0) = p − 1`, `K(0,v) = K(u,0) = −1` | `Rect.lean`: `K_zero_zero`, `K_zero_left`, `K_zero_right` |
| Lemma 3 (rectangles): the expansion with `K + 1`, the geometric-series and sine bounds, the bound | `Rect.lean`: `N_main`, `norm_F_le`, `inv_sin_le`, `sum_norm_F_le`, `rect` |
| Lemma 4 (staircase): one column, columns summed | `Stair.lean`: `column`, `stair` |
| Divisor bound `d(n) ≤ D n^ε` | `Div.lean`: `divisor_bound` |
| Lemma 5: `R(m) ≤ ∑ d(1 + kp) ≤ (m/p) D (1+m)^ε` | `Bound.lean`: `R_le_div`, `R_le` |
| Lemma 2 (`|C(p) − 4| ≤ 8/√p`) and the factorisation of the all-pairs sum | `Sums.lean`: `sum_w_bounds`, `C_close`, `grid_sum` |
| The layer-cake identity, `T(X)` as a pair count | `Sums.lean`: `layer`, `Tc_eq` |
| Identity (2) | `Bound.lean`: `key_identity` |
| The final inequality before the choice of parameters | `Bound.lean`: `main_ineq` |
| Theorem 1 | `Limit.lean`: `rate`, `tendsto_five` |

Inverses are taken as `((a : ZMod p)⁻¹).val`. In Lean, `R` counts `a ∈ [2, p)`, and `Rc = R + 1` also
counts `a = 1`. `rate` uses the divisor bound with exponent `ε/4` and `log p ≤ p^(ε/2)/(ε/2)`, so its
statement has `p^(−1/8+ε)` directly.

Every result uses only propext, Classical.choice and Quot.sound (axiom-validation.txt). The folder was
compiled in an isolated build without the development cache (build-validation.log).
