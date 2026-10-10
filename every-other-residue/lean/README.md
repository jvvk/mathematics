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
definition, statement or constant and checks that the file no longer compiles.

**The encoding.** The sets are `A = {elt k e r}` and `B = {elt k f r}` for `r < 2^k`, where
`elt k e r = r + 2^k * e r`; `par k e f` is the parity of `∑ (e r + f r)`. A matching is a map `σ` that is
injective on `{0, …, 2^k - 1}` and maps it into itself (`IsPerm`), and `Good k e f σ q` says that the sums
`elt k e r + elt k f (σ r)` are pairwise different modulo `2^(k+1)` and all have parity `q`.

| Paper | Lean (namespace `PowerTwoMatching`, file `Basic.lean`) |
|---|---|
| The parity identities of the halving step | `par_split` |
| Halving congruences modulo `2^(k+2)` | `mod_double`, `mod_double_add_one` |
| Theorem, first statement (the matching of parity `p`) | `exists_matching` |
| The residues of parity `q` below `2n`: count and total | `card_parity`, `sum_parity` |
| Theorem, second statement (no matching of parity `1 − p`) | `parity_forced` |
| Section 2: the sums are never distinct modulo `2^k` (`k ≥ 1`) | `not_distinct_mod` |

`exists_matching` and `parity_forced` hold for any `e, f : ℕ → ℕ`, not only bit vectors.

Every result uses only propext, Classical.choice and Quot.sound (axiom-validation.txt). The folder was
compiled in an isolated build without the development cache (build-validation.log).
