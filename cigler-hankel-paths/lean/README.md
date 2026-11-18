# Lean proof sources

Lean 4.34.0; Mathlib is pinned by lake-manifest.json to
5ed2965256430c3649e86755f9576b54eca72435 (v4.34.0).
SOURCE-SNAPSHOT.json records the development commit and the hash of every file. Build caches are excluded.

    lake exe cache get
    lake build LeanProofs
    lake env lean CheckClaims.lean
    python3 -I scripts/mutate.py scripts/mutants.toml

The first command fetches the pinned Mathlib cache, the second compiles the proofs, the third prints the
statements and axioms of the headline results, and the last runs the mutation tests: after a passing control
build, each of 66 mutants plants one wrong definition or claim and must stop the build with a Lean error
(timeouts, crashes and missing tools count as inconclusive). Run `lake build LeanProofs` afterwards.

Everything is stated over an arbitrary commutative ring `R`, so `x` and `c` may be indeterminates.

| Paper | Lean (namespace `Hankel456683`) |
|---|---|
| Weighted path counts `a_{n,k}`, `W_j(l → k)`, the weights `s_0 = c + x`, `s_l = c` | `Walks.lean`: `walk`, `walk_succ`, `walk_add`; `Defs.lean`: `ciglerS`, `D` |
| The matrix `H_{k,n}(x)`, verbatim from Cigler's definition | `Defs.lean`: `ciglerH`; `Step3.lean`: `ciglerH_eq` (its closed form (2)), `band_iff`, `above_iff` |
| Section 2: the binomial transform (1) and `L A L^T`, `det L = 1` | `Step1.lean`: `binomial_eq_E`, `hankel_binomial`, `det_L`, `D_indep` |
| Section 2, remark: adding a constant to every horizontal weight | `Step1.lean`: `det_hankel_add_const`; `Headline.lean`: `headline_any_weights` |
| Lemma 1 (cutting the paths) | `Step2.lean`: `hankel_eq_P_mul_W`, `det_P`, `det_hankel_eq_det_W` |
| Identity (4) and its two shift facts | `Step3.lean`: `hE_succ_succ`, `hE_row_zero`, `local_identity` |
| Ballot numbers and `det U = 1` | `Step3.lean`: `ballot_zero`, `ballot_succ`, `ballot_eq_zero_of_lt`, `ballot_self` |
| Lemma 2 (`W = H U`) and Theorem 1 | `Step3.lean`: `walk_eq_sum_hE_ballot`, `det_U`, `W_eq_H_mul_U`, `det_W_eq_det_ciglerH`; `Headline.lean`: `D_eq_det_ciglerH`, `headline` |
| Example 1 and the displayed `H_{2,6}(x)` | `Headline.lean`: `D_one_three`, `ciglerH_two_six` |

Not formalised: Cigler's quadratic recurrence (open; checked numerically in `../verify/check.py`). Every result
uses only propext, Classical.choice and Quot.sound (axiom-validation.txt). The folder was compiled in an
isolated build without the development cache (build-validation.log).
