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

| Paper | Lean (namespace `ZeroSumGame`) |
|---|---|
| Section 2: zero transversals, deletion form, finite union of rational subspaces | `Dimension.lean`: `Winning`, `winning_iff_hits`, `winning_iff_mem_template`, `winning_finite_union` |
| Lemma 4 (rank lemma) | `Dimension.lean`: `incidence_rank_bound` |
| Theorem 1 (both bounds, arbitrary `N`, `k`; the square game; affine families) | `Dimension.lean`: `sharp_dimension_theorem`, `square_sharp_dimension`, `winning_affine_family_dimension_bound` |
| Lemma 7 (order-three criterion) | `Order3.lean`: `order3_criterion` |
| Lemma 8 (collisions) and its converse | `Gaps.lean`: `collision`, `coll_two` |
| Theorem 2, distinct entries, in normalised form | `Gaps.lean`: `three_values`, `win_iff_two`, `order3_distinct` |
| Proposition 9 (two-valued normal form) | `TwoValued.lean`: `two_valued` |

`Dimension.lean` was written by Codex; `Order3.lean`, `Gaps.lean` and `TwoValued.lean` by Claude. In `Gaps.lean`
the matrix is normalised to second row `(0, p, p+q)` and third row `(0, r, r+s)` with positive gaps; the
reduction of an arbitrary matrix with distinct entries to this form (translation and reordering within rows)
is by hand. `order3_distinct` states: winning iff the gaps satisfy one of the five family relations `Fam` and
every `-a_i` is a coincidence value.

Not formalised: the bookkeeping of the hardness reduction, the twelve order-three families and the count of
1107 components (checked by `../verify/recheck.py`), and Remarks 5 and 6. Every result uses only propext,
Classical.choice and Quot.sound (axiom-validation.txt). The folder was compiled in an isolated build without
the development cache (build-validation.log).
