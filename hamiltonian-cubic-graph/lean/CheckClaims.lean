import LeanProofs

open CubicK23
-- the graph: twenty vertices, cubic
#print axioms card_V
#print axioms cubic
-- Hamiltonian: an explicit cycle through all twenty vertices
#print axioms hamiltonian
-- not bipartite: an explicit 9-cycle, and no proper 2-colouring
#print axioms oddCycle_isCycle
#print axioms not_bipartite
-- the main theorem: no cycle of length nineteen
#check @no_cycle_nineteen
#print axioms no_cycle_nineteen
