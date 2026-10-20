# SpectreCover (MO 516016)

A periodic 12-fold cover of the plane by copies of the Spectre `Tile(1,1)`, using rotations and
translations only.

**Main theorem** (`Main.lean`, `spectre_twelve_fold`): for the 54 placements of the answer and
every vector of the period lattice, almost every point of the plane lies in exactly 12 tiles.
Axioms: `propext`, `Classical.choice`, `Quot.sound` (no `native_decide`).

| File | Content |
|---|---|
| `Shadow.lean` | shadow of an oriented segment; indicator of a ccw triangle = sum of edge shadows (`tri_shadow`) |
| `Cover.lean` | abstract periodic triangle family; edge pairing makes the count constant on vertical lines (`vmove`) |
| `Ae.lean` | horizontal move by swapping coordinates; null exceptional set; count a.e. constant (`cnt_ae_const`) |
| `Count.lean` | triangle area, period-cell area, unfolding over the cell: `c · covol = Σ area` (`count_mul_det`) |
| `Data.lean` | the Spectre in `ℤ[ζ]`, triangulation, 54 placements; kernel-checked certificates |
| `Concrete.lean` | `ℤ[ζ]` to the plane; orientations in `ℚ(√3)`; the family meets every hypothesis |
| `Main.lean` | constant is 12; tiles as rigid images of the Spectre; no overlap inside a tile; main theorem |

Kernel certificates (`decide +kernel`): the 1944 triangle edges cancel modulo the lattice
(`keys_sorted_eq`); every triangle is counterclockwise (`all_ccw`); triangles of one tile are
separated by an edge line (`tiles_separated`); the triangulation's boundary is the 14-gon
(`tris_boundary`); placements are distinct; Codex's 378 + 378 curved-edge records cancel
(`curved_records_cancel`).

**Scope.** The analytic theorem is for the straight-edged `Tile(1,1)`. For curved Spectres only
the combinatorial certificate is checked; the step from it to constant coverage would need the
Jordan curve theorem for the edge curve. Minimality of 12 is not claimed.

Mutation harness: `scripts/spectrecover_mutants.py`.
