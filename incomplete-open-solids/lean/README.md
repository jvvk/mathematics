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

**Scope.** Lean checks the finite numbers the paper uses. Burnside's lemma (the number of classes is the
average number of fixed sets) and the case analyses that turn these numbers into the counts of Table 1 are
in the paper and are not formalised; the Python audits in `verify/` check them exhaustively.

**The encoding.** Graphs are lists of edges `(a, b)` with `a < b`. Cube vertices are `0, …, 7` read as three
bits, joined when they differ in one bit; octahedron vertices `2i` and `2i + 1` are `±eᵢ`, joined unless
antipodal; the tetrahedron is all pairs of `0, …, 3`. The graphs of the paper are obtained with `delete`,
not typed in. `IsTree M t` says that `t` has `|M| - 1` edges, covers the vertex set `M` and is connected
(checked by growing the reached set eight times), which characterises spanning trees of `M`. The rotations
are the 24 coordinate permutations with sign changes of determinant `+1`, acting on both solids
(`cubeMap`, `octMap`). The small facts are proved by `decide +kernel`, kernel reduction with no extra
axioms, on graphs with at most twelve edges.

| Paper | Lean (namespace `OpenSolids`, file `Basic.lean`) |
|---|---|
| The solids have 12, 12 and 6 edges; 24 rotations, all symmetries of both solids | `cube_size`, `rot_count`, `rot_preserve` |
| Cycle types of the rotations on the edges, the same for both solids | `cube_cycle_profile` |
| The polynomial `Z(t)`, equation (1) | `cube_burnside` |
| Cube: 4, 5, 6 vertices span at most 4, 5, 7 edges | `cube_induced` |
| Octahedron: 2, 3, 4 vertices span at most 1, 3, 5 edges; 5 exactly with one antipodal pair | `oct_induced` |
| Cube, five edges: ladder 15 trees, fixed 3 | `ladder_trees`, `ladder_fixed` |
| Cube, five edges: square with leaves 4 trees, fixed 0 | `square_leaves_trees`, `square_leaves_fixed` |
| Cube, five edges: hexagon 6 trees, fixed 0, 0, 2, 2, 2 | `hexagon_trees`, `hexagon_fixed` |
| Cube, six edges: hexagon with hub, 18 + 24 + 8 = 50 trees by spokes, fixed 2, 2 | `hub_trees`, `hub_fixed` |
| Octahedron, four edges: wheel, 16 + 20 + 8 + 1 = 45 trees by spokes, fixed 1, 1, 5 | `wheel_trees`, `wheel_fixed` |
| Octahedron, three edges: `K₄` minus an edge, 8 trees, fixed 2 | `k4e_trees`, `k4e_fixed` |
| Tetrahedron: 16 trees of `K₄`, 4 stars | `k4_trees` |
| The averages, corrections and totals 122, 185, 6 | `cube_total`, `octahedron_total`, `tetrahedron_total` |

Every result uses at most propext, Classical.choice and Quot.sound (axiom-validation.txt). The folder was
compiled in an isolated build without the development cache (build-validation.log).
