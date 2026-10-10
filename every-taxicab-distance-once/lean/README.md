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
statement, constant or point and checks that the file no longer compiles.

**The statement.** `Realises P N` says that the taxicab distances of the pairs `i < j` of the points
`P : Fin n → ℤ × ℤ` are pairwise different and form the set `{1, …, N}`.

| Paper | Lean (namespace `TaxicabEleven`, file `Basic.lean`) |
|---|---|
| A distance is odd iff its endpoints have different colours | `odd_tdist_iff` |
| The cross pairs number `ab` | `card_cross` |
| `1, …, N` contains `⌈N/2⌉ = (N + 1)/2` odd numbers | `card_odd_Icc` |
| `N` is even iff `n ≡ 0, 1 (mod 4)` | `choose_two_even_iff` |
| Theorem 1: `(a − b)² = n − 2 (N mod 2)` | `parity` |
| Theorem 1: `n` or `n − 2` is a perfect square | `square_condition` |
| Proposition 2: the eleven points realise `55` | `eleven` |
| Their colour split is `7, 4` | `eleven_split` |

`eleven` and `eleven_split` are finite checks (`decide`), the same checks the paper's table lets a reader do by
hand. Injectivity follows from the image having 55 elements, as many as there are pairs.

Every result uses only propext, Classical.choice and Quot.sound (axiom-validation.txt). The folder was
compiled in an isolated build without the development cache (build-validation.log).
