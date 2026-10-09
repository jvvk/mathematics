# Lean formalisation: a Hamiltonian cubic graph with no cycle of length n − 1

Lean 4.34.0 with Mathlib v4.34.0. Build with `lake exe cache get && lake build LeanProofs`, then
`lake env lean CheckClaims.lean` prints each result's axioms (only `propext`, `Classical.choice`,
`Quot.sound`). `python3 scripts/mutants.py` checks that six wrong variants fail to compile.

| Note | Lean (namespace `CubicK23`, file `LeanProofs/CubicK23.lean`) |
|---|---|
| The graph: twenty vertices, `K₄` with each vertex replaced by `K_{2,3}` | `V`, `partner`, `adjB`, `G`, `card_V` |
| It is cubic | `cubic` |
| It is Hamiltonian (an explicit cycle) | `hamCycle`, `hamiltonian` |
| It is not bipartite (an explicit 9-cycle; no proper 2-colouring) | `oddCycle`, `oddCycle_isCycle`, `not_bipartite` |
| Theorem: no cycle of length nineteen | `no_cycle_nineteen` |
| Step 1: neighbourhoods inside a block | `adj_inner`, `adj_attach`, `partner_block_ne` |
| Step 2: the degree count in the block of the missing vertex | inside `no_cycle_nineteen` (the `omega` step) |
| Step 3: a cycle with no edge leaving the block stays in it | inside `no_cycle_nineteen` (`hclosed`, `hfwd`) |

The finite facts about the fixed twenty-vertex graph (degrees, neighbourhoods, the two explicit cycles)
are checked by `decide`. The theorem about cycles is proved for every cycle, as `SimpleGraph.Walk.IsCycle`
in Mathlib, by the counting argument of the note; no enumeration of cycles is involved.

The general construction for any Hamiltonian non-bipartite cubic skeleton is proved by hand in the note
and is not formalised; the formalisation covers the twenty-vertex instance.
