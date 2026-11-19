# Lean formalisation: Monotonicity of a ratio of complete homogeneous symmetric polynomials

Lean 4 (v4.34.0) with Mathlib `v4.34.0`. Every theorem below depends only on `propext`, `Classical.choice` and
`Quot.sound`; `SymmetricRatio/Audit.lean` prints the axioms of each one when it is compiled. Indexing: Lean writes
`n = N + 1`, and `P N y ℓ` is the paper's `P_ℓ` (coefficients `C(N+ℓ, ℓ-k) y^k`).

| Paper | Lean | File |
|---|---|---|
| `h_ℓ` (Mathlib's `MvPolynomial.hsymm`) and `H_i` | `h`, `S`, `vec` | `Bridge.lean` |
| Lemma 1: `P_ℓ(i) = H_i(x)`; degree, leading coefficient, positivity on `[0, ∞)` | `h_eq_H`, `H_eq_P`, `natDegree_P`, `leadingCoeff_P`, `P_eval_pos` | `Bridge.lean`, `Main.lean`, `Basic.lean` |
| Lemma 2 (the `x`-derivative identity) | `HP_deriv`, `H_deriv_id` | `Main.lean` |
| Lemma 4 (recurrence (3), shifted by one) | `P_rec` | `Basic.lean` |
| Lemma 5: recursion (4) for `D_ℓ` (here `W`), `D_ℓ > 0`, real negative zeros | `W_rec`, `W_pos`, `real_rooted` | `Basic.lean`, `Roots.lean` |
| Positive weights and the second difference of `f` | `second_difference_pos` | `Convex.lean` |
| Proposition 3 and **Theorem 1** | `psi_strictMonoOn`, `ait_haddou` | `Main.lean`, `Bridge.lean` |

Route: the formalisation follows the paper except in two places. `P_ℓ(i) = H_i` is proved through the Pascal
recursion for `h_ℓ` (`Hf_rec`) rather than the generating function (2), and the recurrence (3) is proved
coefficient by coefficient. The case `ℓ = 1`, the symmetry `x ↦ 1/x` and the Meixner identification are checked by
`../verify/verify_paper.py` for integer `n`, not here. The extension to real `n` in Remark 1 is proved only on
paper: both Lean and the Python checks take `n` to be an integer.

## Build

```
lake exe cache get     # Mathlib build cache
lake build             # compiles every module and runs the axiom audit
python3 -I scripts/mutate.py scripts/mutants.toml   # eleven mutants, each rejected with an error in the mutated copy
```
