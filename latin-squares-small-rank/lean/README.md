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

| Paper | Lean (namespace `LatinRank`) |
|---|---|
| Lemma 3 (orthonormal factorisation, for any subspace containing the columns) | `Factor.lean`: `col`, `factor` |
| Latin squares, `V`, the centred matrix `C`, line sums and squared lengths | `Bound.lean`: `IsLatin`, `V`, `C`, `col_sum_C`, `col_sq_C`, `row_sum_V` |
| The subspace `K = W ∩ 1ᗮ`, `dim K = rank V − 1` | `Bound.lean`: `W`, `K`, `one_mem_W`, `col_C_mem_W`, `col_C_orth`, `finrank_K` |
| Theorem 1 | `Bound.lean`: `rank_bound` (with `d = dim K`), `rank_bound_strict` |
| Corollary 2 | `Bound.lean`: `four_le_rank`, `three_le_rank` |
| `r(4) = 3`, `r(6) = 4`, `r(8) = 4` | `Witness.lean`: `r4`, `r6`, `r8` |

A Latin square is stored with symbols `0, …, n − 1` (`Matrix (Fin n) (Fin n) (Fin n)`, rows and columns
bijective); `V L` adds `1` to every entry, giving the matrix of the paper. Theorem 1 is stated as
`3(n − 1) ≤ (n + 1) dim K`, which is the paper's inequality by `finrank_K`. The witnesses are checked to be
Latin and to factor as `A B` over `ℤ` by `decide`; the factorisations come from `../verify/factorise.py`
(for orders 4 and 8, the exclusive-or construction of the question).

Not formalised: `r(5) = 5` and `r(7) = 6`, which rest on `../verify/certify_minrank.py` (an exhaustive
computation over isotopy representatives with an exact modular certificate). Every result uses only
propext, Classical.choice and Quot.sound (axiom-validation.txt). The folder was compiled in an isolated
build without the development cache (build-validation.log).
