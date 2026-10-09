# A Hamiltonian cubic graph with no cycle of length n − 1

<!-- visual:start -->
<p align="center"><img src="https://raw.githubusercontent.com/jvvk/jvvk/c7403d6bbbc7106e1780d8c34833854afcb0116f/assets/cubic.svg" width="760" alt="A cubic graph with no (n−1)-cycle"></p>

<p align="center"><b>Hamiltonian, not bipartite, and no cycle of length 19: an answer to Gordon Royle's question.</b><br><sub>Open problem settled · formally verified in Lean 4</sub></p>

<p align="center"><sub><a href="paper">paper</a> · <a href="lean">Lean proof</a> · <a href="verify">code</a> · <a href="../">all results</a></sub></p>
<!-- visual:end -->

Gordon Royle asked on MathOverflow ([question 263706](https://mathoverflow.net/q/263706), 2017) whether a cubic graph on `n` vertices can be Hamiltonian, not bipartite, and have no cycle of length `n − 1`, and reported that his computer found none on up to 24 vertices.

Yes, on 20 vertices: take `K₄` and replace each vertex by a copy of `K_{2,3}`, attaching the three edges at that vertex to the three vertices of the larger class (Theorem 1). The graph is cubic; it is Hamiltonian, since any two attachments of a block are joined by a path through all five of its vertices; and a triangle of `K₄` becomes a 9-cycle. It has no 19-cycle by a count of cycle edges in the block of the missing vertex: twice the edges inside plus the edges leaving is eight, and the edges inside are twice the inner vertices on the cycle. So either four edges leave through three attachments, or none leave and the cycle is trapped in five vertices. The argument works with any Hamiltonian non-bipartite cubic graph in place of `K₄` (the prism gives 30 vertices). Why the reported search missed the example is not known; it has girth 4 and 3-edge cuts.

Preprint v1, 9 October 2026, not peer reviewed. For the 20-vertex graph every statement of Theorem 1 is formally verified in Lean 4 (`lean/`, standard axioms only): the theorem about cycles is proved for every cycle by the counting argument, and only the finite facts about the fixed graph are checked by evaluation. An independent exhaustive search confirms the result. The author used an AI tool (Claude, Anthropic) in this work, as described in the note, and is responsible for its content.

## Contents

- `paper/`: `note.tex`, `note.pdf`, and `make_fig.py`, which draws the graph with its Hamiltonian cycle and 9-cycle after checking that the graph is cubic and both cycles are valid.
- `lean/`: a Lake project pinned to Lean 4.34.0 and Mathlib v4.34.0. `lean/README.md` maps each statement to its Lean name; `CheckClaims.lean` prints their axioms; `scripts/mutants.py` checks that six wrong variants fail to compile; `build-validation.log` records an isolated build.
- `verify/check_cycles.py`: builds the graph independently (with `networkx`) and checks by exhaustive search that deleting any vertex leaves a non-Hamiltonian graph, with the cube and the prism as controls, and the 30-vertex example from the prism.

## Reproduce

```
cd lean && lake exe cache get && lake build LeanProofs && lake env lean CheckClaims.lean
python3 scripts/mutants.py
cd ../verify && python3 check_cycles.py
cd ../paper && python3 make_fig.py && latexmk -pdf note.tex
```
