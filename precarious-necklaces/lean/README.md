# Lean proof sources

Lean 4.34.0; Mathlib is pinned by lake-manifest.json to
5ed2965256430c3649e86755f9576b54eca72435 (v4.34.0).
SOURCE-SNAPSHOT.json records the development commit and the hash of every file. Build caches are excluded.

    lake exe cache get
    lake build LeanProofs
    lake env lean CheckClaims.lean
    python3 scripts/mutants.py

The first command fetches the pinned Mathlib cache, the second compiles the proofs, the third prints the
statements and axioms of the results below, and the last runs the 39 mutation tests: each plants one wrong
bound, exponent, hypothesis or definition and checks that the files no longer compile.

| Paper | Lean (namespace `Precarious`) |
|---|---|
| Words, proper powers (`Symm`), deletion, pair projection, precarious | `Basic.lean`: `IsPow`, `Symm`, `del`, `pair`, `IsPrecarious` |
| Keeping a set of colours; `s`-precarious | `Framework.lean`: `keep`, `KeepPrec` |
| Lemma 1 (fixed by a rotation iff a proper power; rotation commutes with projection) | `Rotation.lean`: `symm_iff_rotate`, `symm_rotate`, `filter_rotate` |
| Lemma 2 (exponent divides every count) | `Basic.lean`: `count_dvd_of_pow` |
| Lemma 3 (two-letter projections decide `q`-th powers) | `Basic.lean`: `pow_of_pairs` |
| Section 3, constructions for `s = k − 1` | `Construct.lean`: `even_spec`, `odd_spec` |
| Section 3, odd `s` (pair rhythms plus fixed colours) | `Extensions.lean`: `extWord_keepPrec`, `extWord_not_symm` |
| Section 3, even `s` (clusters before groups of blocks) | `ClosedConstruct.lean`: `clusterWord_keepPrec`, `clusterWord_not_symm` |
| The remark (every nonempty deletion is symmetric) | `Extensions.lean`: `even_every_deletion`, `odd_every_deletion` |
| Section 4, lower bound for `s = k − 1` | `Bound.lean`: `lower_bound` |
| Section 4, lower bound for every `s` (avoided pairs, light and heavy colours) | `Closed.lean`: `keep_general_bound` |
| Theorem 1 | `Construct.lean`: `precarious_min` |
| Theorem 2 | `ClosedConstruct.lean`: `keep_exact` |
| Theorem 2 at `s = k − 1` is Theorem 1 | `ClosedConstruct.lean`: `closedForm_top`, `isPrecarious_iff_keepPrec` |
| The cases `s = 2` (`2k + 8`) and `s = 3` (`6k`) | `Extensions.lean`: `keep_two_exact`, `keep_three_exact` |
| `a(2), …, a(7) = 4, 14, 24, 126, 180, 1290` | `Bound.lean`: `a_values` |

A necklace is a word read up to rotation; `symm_iff_rotate` and `symm_rotate` show that working with words
loses nothing. Primes are indexed by `Nat.nth Nat.Prime`, and `pr m` is the product of the first `m`.

Nothing is assumed: every result above uses only propext, Classical.choice and Quot.sound
(axiom-validation.txt). The folder was compiled in an isolated build without the development cache
(build-validation.log).
