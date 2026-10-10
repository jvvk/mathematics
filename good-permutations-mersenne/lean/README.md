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

| Paper | Lean (namespace `GoodPerm`) |
|---|---|
| Block sums, permutations of `1..n`, good permutations | `Basic.lean`: `S`, `IsPerm`, `Good` |
| Lemma 4 (blocks of length `2^k` sum to an odd multiple of `2^(k−1)`; te4's congruence) | `Mersenne.lean`: `two_adic`, `congr_shift` |
| Partners differ by `q`; the middle block's sum | `Mersenne.lean`: `pair_gap`, `middle_sum` |
| Theorem 1 (Bîsceanu: only `n = 2^m − 1`) | `Mersenne.lean`: `mersenne` |
| Corollary 5 (the search reduction) | `Mersenne.lean`: `reduction` |
| The asker's permutation (1) and closed form (2); it is a permutation | `Construction.lean`: `c`, `c_perm` |
| Theorem 2: blocks away from the start, odd and even prefixes | `Construction.lean`: `interior`, `S_prefix_odd`, `prefix_even_not_dvd`, `block_dvd_iff` |
| Theorem 2: good iff `n` prime | `Construction.lean`: `good_iff_prime` |

Positions run from `1` to `n` and values are integers; a permutation is a function that maps `1..n`
injectively into `1..n`. In `middle_sum` the middle block is handled through its sum (total minus the
pairs), which is what the proof of Theorem 1 uses.

Not formalised: the exhaustive searches of Theorem 3 (C programs in `verify/`, run on the structure that
`reduction` proves). Every result uses only propext, Classical.choice and Quot.sound
(axiom-validation.txt). The folder was compiled in an isolated build without the development cache
(build-validation.log).
