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
constant, hypothesis or definition and checks that the file no longer compiles.

| Paper | Lean (namespace `StanleySylow`) |
|---|---|
| Lemma 1 (quadratic composition over a finite field, with the norm computation) | `Question.lean`: `norm_sub_eval`, `monic_comp_quad` |
| Section 3, the scaled recurrence as composition with a quadratic | `Sylow.lean`: `Ps_succ_comp`; `Question.lean`: `f_succ_comp` |
| Section 4, the factorization of the Sylow polynomials | `Sylow.lean`: `AS_comp`, `BS_comp`, `sylow_factorization`, `sylow_factors_monic`, `sylow_factors_degree` |
| Section 4, agreement of the top coefficients | `Sylow.lean`: `sylow_top_coeffs_agree`, `top_coeffs_agree` |
| Section 5, the critical orbit modulo 5 and the induction | `Question.lean`: `tower`, `tower_properties`; `Sylow.lean`: `tail1_irred` |
| Theorem 1 (irreducibility over F_5, Z, Q for every n) | `Sylow.lean`: `sylow_irreducible_mod5`, `sylow_irreducible_rat` |
| Section 6, Corollary (the polynomials as printed) | `Question.lean`: `stanleyF_recurrence`, `stanley_factorization`, `stanley_factors_degree`, `stanley_irreducible_mod5`, `stanley_irreducible_rat` |

Indexing: `Ps n` is the paper's `P_n` and `a n = 2^(2^n - 1)` is `c_n = |G_{2^n}|`; `AS n`, `BS n` are the
paper's `A_{n+2}`, `B_{n+2}`. In `Question.lean` (written by Codex), `f n` is the question's `f_{n+1}` and
the `stanley_*` statements use the question's own indexing. Modulo 5 the Lean proof works with the unscaled
recurrence `P ↦ P² + c_n P`, which is the monic quadratic `x² + 3x` once `c_n ≡ 3`; it is conjugate to `T` by
the scaling `P_n = c_n T^n(q)`, so its critical value is `4` and its critical orbit `4 → 3 → 3` replaces
`3 → 1 → 1`.

Not formalised: the identification of `P_n` with the cycle count of the Sylow subgroup (the classical
wreath-product recurrence, proved in Section 2 and checked by listing the group in `../verify/recheck.py`),
and the odd-prime data of Section 7. Every result uses only propext, Classical.choice and Quot.sound
(axiom-validation.txt). The folder was compiled in an isolated build without the development cache
(build-validation.log).
