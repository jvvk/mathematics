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

| Paper | Lean (namespace `CubeUnfoldings`) |
|---|---|
| Tiling by translates of a set of cells, exactly once | `Quotients.lean`: `TilesBy`, `tilesBy_ker_iff`, `tilesBy_ker_iff_card` |
| Lemma 3 (lattice tilings) | `Quotients.lean`: `tiles_one_iff` |
| Lemma 4 (two tiles) | `Quotients.lean`: `TilesTwo`, `tiles_two_iff` |
| Lemma 5 (`P` and `t − P`; the sumset `A + A`) | `Quotients.lean`: `refl`, `tiles_refl_iff`, `exists_tiles_refl_iff` |
| Example 6 (an unfolding of the five-cube, `ℤ₂ × ℤ₁₀`) | `Example.lean`: `P5`, `φ5`, `t5`, `example_five` |

The sublattice is the kernel of a homomorphism `φ` from an additive group onto a finite group `G`, which is
how the paper uses Lemmas 3 to 5 (every sublattice of finite index is such a kernel). The second tile `−P + t`
of the paper is `refl P t = t − P`, the same set.

In Example 6 the finite facts (`φ` is injective on the ten cells, `φ(t) ∉ φ(P) + φ(P)`, the list of images)
are checked by `decide`, as the paper checks them by listing the twenty images.

Not formalised: the enumeration of unfoldings and the 9,694 + 502,110 certificates. They are checked by
`../verify/verify2.py` and the other programs in `../verify/`, which share no code with the searches.
Every result uses only propext, Classical.choice and Quot.sound (axiom-validation.txt). The folder was
compiled in an isolated build without the development cache (build-validation.log).
