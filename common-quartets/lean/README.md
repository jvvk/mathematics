# Lean proof sources

Lean 4.34.0; Mathlib is pinned by lake-manifest.json to
5ed2965256430c3649e86755f9576b54eca72435 (v4.34.0).
SOURCE-SNAPSHOT.json records the development commit and the hash of every file. Build caches are excluded.

    lake exe cache get
    lake build LeanProofs
    lake env lean CheckClaims.lean
    python3 scripts/mutants.py

The first command fetches the pinned Mathlib cache, the second compiles the proofs, the third prints the
statements and axioms of the results below, and the last runs the 17 mutation tests: each plants one wrong
threshold, constant, caterpillar or leaf label and checks that the file no longer compiles.

| Paper | Lean |
|---|---|
| Lemma 2.2 (Spencer's cell lemma) | `QuartetIter.lean`: `QuartetIter.cell` |
| Proposition 3.1 (the iteration), one step and all `k` | `QuartetIter.lean`: `QuartetIter.step`, `QuartetIter.iterate` |
| Theorem 1.2, upper bound `h(k) ≤ 2·3ᵏ⁻¹ + 1` | `QuartetIter.lean`: `QuartetIter.common_quartet` |
| Definition 4.1 and Theorem 4.2 (`F_k` has no common quartet, every `k`) | `CatFamily.lean`: `CatFamily.pos`, `CatFamily.family` |
| Proposition 5.1 (`T`, `3T`, `9T` on `ℤ₁₃`) | `CommonQuartet.lean`: `cyclic_leaves`, `cyclic_binary`, `cyclic_no_common_quartet` |
| A second 13-leaf triple, found without the symmetry | `CommonQuartet.lean`: `witness_leaves`, `witness_binary`, `no_common_quartet` |
| `C(13, 4) = 715` quartets | `CommonQuartet.lean`: `quads_card` |

**What is abstracted.** In `QuartetIter.lean` a tree is a split system `SplitSys`: a relation `Sep X Y`
("some edge has `X` on one side and `Y` on the other") with three fields that are taken as given, namely that
separation passes to subsets, is symmetric, and that every leaf set `U` with `|U| ≥ 2` has a separated split
with both sides at least `|U|/3`. These are the facts of Section 2 for a tree restricted to `U` (Lemma 2.1 and the
paragraph before it); they are not derived from a graph-theoretic definition of a tree here. Spencer's lemma and the
iteration are proved from them.

In `CatFamily.lean` a caterpillar is its leaf order, given by a position map on the integers `−h, …, h`; the
order `none` is `π₀` and `some b` is `π_{b+1}`. In `CommonQuartet.lean` a tree is a rooted binary term with leaf 0
on the pendant edge of the root, and a quartet `ab|cd` is displayed when some subtree meets `{a, b, c, d}` in
exactly two leaves; the three facts are checked by `decide +kernel` over all 715 quartets.

Not formalised: the upper bound `h(3) ≤ 14` (Snir and Yuster's theorem, confirmed by the SAT search with LRAT
proofs in `verify/`), the 21-leaf example for `k = 4` and the classification of Proposition 5.2 (both in
`verify/`). Every result above uses only Lean's standard axioms; the `decide` checks use none
(axiom-validation.txt). The folder was compiled in an isolated build without the development cache
(build-validation.log).
