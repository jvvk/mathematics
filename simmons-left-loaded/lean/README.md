# Lean formalisation: what is and is not proved

Lean 4 + Mathlib, namespace `SimmonsPartial`, files in `LeanProofs/SimmonsPartial/`. Build: `lake exe cache get && lake build`;
`lake env lean CheckClaims.lean` prints the axioms of every result below (recorded in `axiom-validation.txt`). Every
result depends only on propext, Classical.choice and Quot.sound, or a subset of them. No sorry, no decide, no
native_decide.

Everything is in integer arithmetic. With `q = n − m`, the weights are `w n m j = C(n, j) m^j q^(n−j)` (so that
`P(X = j) = w n m j / n^n` for `X ~ Bin(n, m/n)`), `A n m i = n^n α_i`, and `d n m i = n^n (P(X = m+i) − P(X = m−i))`.

## Proved
| Paper | Lean | Scope |
|---|---|---|
| `α_i` is the binomial difference | `alpha_eq` | `A n m i / n^n` equals `P(X ≤ m−i) − P(X ≥ m+i)` for the real binomial probabilities, `m ≤ n`, `n > 0` |
| ratio of consecutive probabilities | `adjacent` | `(j+1) q w(j+1) = (n−j) m w(j)` |
| equation (2) | `A_succ` | `A (i+1) = A i + d i` |
| the zero total | `mean`, `total` | `E X = m` in weights, and `∑_{i=1}^{n−m} A i = 0` for `n ≥ 2m` |
| `α_q = −p_n` | `A_last` | `A (n−m) = −w n` when `m < n − m` |
| Lemma 3.1 | `ratio`, `factor` | the ratio identity, multiplied out, and the factorisation `(q−m)((q+m)i(i+1) − mq)` |
| the sign pattern of `d` | `neg_start`, `d_step` | `d` is negative and then positive |
| the shape argument (Lemma 2.2, finite form) | `up`, `down`, `neg_persists`, `partial_pos` | for any integer sequence on `1..q` whose rises persist, that ends negative and sums to zero |
| Theorem 1.2 | `partial_sum_pos` | `n > 2m ≥ 2`, `1 ≤ k < n − m`: `∑_{i=1}^k A i > 0` |
| Theorem 1.2, sign change | `one_sign_change`, `neg_persists_A` | once `α_i < 0`, every later `α_j` (up to `m`, and up to `n − m`) is negative |
| Theorem 1.2, `n = 2m` | `w_symm`, `A_symm_zero` | every `α_i` is zero |
| Conjecture 1.1 | `conjecture` | `n ≥ 2m`, `1 ≤ k ≤ m`: `∑_{i=1}^k A i ≥ 0` |

## Not formalised
- Lemma 2.2 in its general form (any nonnegative integer variable with finite integer mean, possibly unbounded): the
  Lean shape lemmas cover the finite case used for the binomial.
- Propositions 4.1 (Poisson) and 4.2 (negative binomial) and Corollary 4.3. `../verify/identities.py` checks the ratio identities
  in Propositions 4.1 and 4.2 symbolically and `../verify/nb_check.py` checks the negative binomial partial sums exactly for
  `r ≤ 6`, `n ≤ 7`; the Poisson partial sums and Corollary 4.3 (which rests on Theorem 1.1 and Lemma 3.2 of
  Fokkink, Papavassiliou and Pelekis) are not checked by program.

## Mutation tests
`scripts/mutants.toml`, run with `cd scripts && python3 mutate.py mutants.toml` (runner included): 14 mutants, all
rejected, all controls pass (`mutation-validation.log`). Each is a false strengthening, with a counterexample in a
comment: the adjacent identity, the value of `α_q`, the mean, the zero total over a shorter range, the ratio identity,
the factorisation, `neg_start` over the whole range, `d_step` with its hypothesis weakened to a tautology, the shape
lemma with `a q ≤ 0`, `partial_sum_pos` at `k = n − m` (where the sum is zero), `one_sign_change` up to `n`, `w_symm`
one step too far, the conjecture with strict inequality at `n = 2m`, and the bridge with `n^(n+1)`.

Pinned versions: `lean-toolchain` and `lake-manifest.json`.
