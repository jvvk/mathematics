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
statement, hypothesis or constant and checks that the file no longer compiles.

**Scope.** These are the steps of the paper that are proved rather than quoted or computed. The splitting
theorem of Conway, Radin and Sadun and the congruence theorem of Graham, Lagarias, Mallows, Wilks and Yan are
cited. The valuation criterion is standard algebraic number theory. The searches behind Theorems 1 and 2 are
Python computations (`../verify`), and by design they stay outside Lean.

| Paper | Lean (namespace `CoinsTray`, file `Basic.lean`) |
|---|---|
| The rim angle: law of cosines (1) | `rim_cos`, `cos_alpha` (`alpha d = arccos (1 − 2/d)`) |
| `α_d` is a rational multiple of `π` only for `d ∈ {1, 2, 4}` (Niven) | `alpha_rat_iff` |
| `n = 5`: the pairs with `d = 6, 8, 12, 16` have irrational angles | `alpha_irrational_n5` |
| The asker's ring: `2α₃ + α₉ = π` | `dan_four` |
| `n = 5`: two halves `120°` apart overlap (`√3/2 < 1`) | `halves_overlap` |
| Proposition 3: the only root quadruple `(−1, b, c, d)` is `(−1, 2, 2, 3)` | `root_unique` |

In `alpha_irrational_n5`, the step from "`α_d` is irrational" to "the pair cannot be a rim neighbour pair"
uses the paper's observation that `d = 6, 8, 12, 16` are alone in their classes, together with the splitting
theorem.

Every result uses only propext, Classical.choice and Quot.sound (axiom-validation.txt). The folder was
compiled in an isolated build without the development cache (build-validation.log).
