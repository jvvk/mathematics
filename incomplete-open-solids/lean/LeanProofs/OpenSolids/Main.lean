import LeanProofs.OpenSolids.Basic

/-!
# Incomplete open solids by hand (MO 508521): axiom report

The finite counts of the note: the 24 rotations and their cycle types (`rot_count`, `rot_preserve`,
`cube_cycle_profile`), the edge-set polynomial (`cube_burnside`), the vertex bounds (`cube_induced`,
`oct_induced`), the spanning trees and their fixed points under each stabiliser, and the three sums.
Burnside's lemma and the case analysis that uses these numbers are in the paper.
-/

#print axioms OpenSolids.cube_size
#print axioms OpenSolids.rot_count
#print axioms OpenSolids.rot_preserve
#print axioms OpenSolids.cube_cycle_profile
#print axioms OpenSolids.cube_burnside
#print axioms OpenSolids.cube_induced
#print axioms OpenSolids.oct_induced
#print axioms OpenSolids.ladder_trees
#print axioms OpenSolids.ladder_fixed
#print axioms OpenSolids.square_leaves_trees
#print axioms OpenSolids.square_leaves_fixed
#print axioms OpenSolids.hexagon_trees
#print axioms OpenSolids.hexagon_fixed
#print axioms OpenSolids.hub_trees
#print axioms OpenSolids.hub_fixed
#print axioms OpenSolids.wheel_trees
#print axioms OpenSolids.wheel_fixed
#print axioms OpenSolids.k4e_trees
#print axioms OpenSolids.k4e_fixed
#print axioms OpenSolids.k4_trees
#print axioms OpenSolids.cube_total
#print axioms OpenSolids.octahedron_total
#print axioms OpenSolids.tetrahedron_total
