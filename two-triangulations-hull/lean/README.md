# Lean proof sources

Lean 4.34.0; Mathlib is pinned by `lake-manifest.json` to
`5ed2965256430c3649e86755f9576b54eca72435` (v4.34.0).
`SOURCE-SNAPSHOT.json` records the source commit and hashes of the exact archived files.
Only this paper's import closure is included; unrelated proofs and local caches are excluded.

From this directory, with elan/Lean installed:

    lake exe cache get
    lake build LeanProofs
    lake env lean CheckClaims.lean

The first command fetches the pinned dependencies and Mathlib's compiled cache.
The second compiles this paper's complete archived proof dependency graph.
The last prints theorem signatures and axiom dependencies. Expected dependencies:
`propext`, `Classical.choice`, `Quot.sound` only. Read theorem parameters as well
as the axiom list: an explicit hypothesis is not reported as an added axiom.

Theorem 1 and regeneration have no enumeration hypothesis. Theorem 2 takes
`TwoTri.Hulls.PentagonGap`: no hull-only pair for a pentagonal hull and n = 6,7,8.
This is the exhaustive database result, not a Lean-proved enumeration.
The convex seed is formalised on parabola points, which suffices for existence.

## Paper to Lean (numbering of the 8 October 2026 manuscript)

- Theorem 1: `TwoTri.theorem1_geometric` (via `TwoTri.upper`).
- Lemma 3 and Corollary 4 (lower bound): `TwoTri.sweep`, `TwoTri.lower`, `TwoTri.six_unavoidable`.
- Lemma 6 (insertion): `TwoTri.insert_isTri`.
- Definition 7 (chain) and Lemma 8 (regeneration of a chain): `TwoTri.Inv` and `TwoTri.step`.
- Lemma 9 (convex seed): `TwoTri.Hulls.isTri_A`, `isTri_B`, `inter_AB`, and the chain `inv_cvx` (h >= 7).
- The seven-point hexagonal example and its chain: `TwoTri.Hulls.Seven.inv7`.
- Theorem 2: `TwoTri.Hulls.theorem2`, with the enumeration hypothesis `PentagonGap`.
- The remark after Theorem 2 (every good pair returns once |P| >= 7): `TwoTri.regeneration`.
