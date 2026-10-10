# Lean formalisation: sixteen words cover all 15-bit strings

Lean 4.34.0 with Mathlib v4.34.0. Build with `lake exe cache get && lake build LeanProofs`, then
`lake env lean CheckClaims.lean` prints each result's axioms (only `propext`, `Classical.choice`,
`Quot.sound`). `python3 scripts/mutants.py` checks that 9 wrong variants fail.

Words are `List Bool`; `Covers S n` says every word of length `n` has a subsequence (`List.Sublist`) in `S`.

| Paper | Lean (namespace `DeletionCover`) |
|---|---|
| Lemma 1 (blocks): concatenations cover `n₁ + n₂`, with at most `|S||T|` words of length `m₁ + m₂` | `covers_append`, `uniform_append`, `card_append_le` |
| The `m`-fold concatenation covers length `15m` with `16^m` words | `covers_pow` |
| `H(n, b)` is attained, positive and submultiplicative | `words`, `covers_words`, `H`, `H_spec`, `H_pos`, `H_mul` |
| Fekete: `log H(3k, k)/k` converges to its infimum (Mathlib's `Subadditive.tendsto_lim`) | `subadditive_log`, `rate_exists` |
| Corollary 1: a sixteen-word cover of length 15 gives `α ≤ 16^(1/15)` | `alpha_le` |
| `1.2030 < 16^(1/15) < 1.2031` and `17^(1/15) > 1.2078` | `rate_16`, `rate_17` |

## What is not formalised

The cover itself (Theorem 1) and Proposition 1 are finite computations, checked by the programs in `verify/`
(two independent cover checks; two solvers and a DRAT proof for Proposition 1). `alpha_le` takes the existence of
the sixteen-word cover as its hypothesis.
