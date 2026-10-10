# Lean formalisation: five numbers, many averages

Lean 4.34.0 with Mathlib v4.34.0. Build with `lake exe cache get && lake build LeanProofs`, then
`lake env lean CheckClaims.lean` prints each result's axioms (only `propext`, `Classical.choice`,
`Quot.sound`). `python3 scripts/mutants.py` checks that 9 wrong variants fail.

A strategy is any function `mv : ℕ → Fin 5 × Fin 5` (move `r` averages the two entries `mv r`), and
`seq x mv r` is the list after `r` moves. Every step of the proof of Theorem 1 is formalised; nothing is quoted.

| Paper | Lean (namespace `PairwiseAveraging`) |
|---|---|
| Lemma 1: after `r` moves each entry is `∑ mᵢ xᵢ / 2^r`, `mᵢ ∈ ℕ`, `∑ mᵢ = 2^r` | `weights` |
| Moves commute with `x ↦ cx + d` and keep the sum | `affine`, `sum_avg`, `sum_seq` |
| Lemma 2: no entry of `B_k` equals `t` before move `k` (the divisibility argument) | `no_congruence`, `no_mean_before` |
| Lemma 3: the count of entries at the mean does not grow or grows by exactly 2, and is never 4 | `count_step`, `count_ne_pred` |
| Theorem 1, lower bound: every strategy needs at least `k + 3` moves | `lower_bound` |
| Theorem 1, upper bound: the strategy of Section 2 (the shrinking triple, then three moves) | `strategy`, `triple`, `upper_bound` |
| Theorem 1: the least number of moves is exactly `k + 3` | `optimum` |
| The integer form `(5N, 0, 4N, 3N + 5ε, 3N + 5ε) = N B_k + 3N` | `integer_version` |
| For `k ≥ 2` no nonempty proper subset of `B_k` has mean `t` | `no_balanced_subset` |
