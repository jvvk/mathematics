# Incomplete open solids by hand

<!-- visual:start -->
<p align="center"><img src="https://raw.githubusercontent.com/jvvk/jvvk/ee7dcd087155fa15f1e48f59ee34cc0ae55f4e01/assets/incomplete-open-solids.svg" width="760" alt="Incomplete open solids by hand"></p>

<p align="center"><b>LeWitt's 122 incomplete open cubes counted with pencil and paper, and the same for the tetrahedron (6) and the octahedron (185): Burnside for many edges, spanning trees after deleting unused vertices for few.</b><br><sub>Answers a question · finite counts in Lean</sub></p>

<p align="center"><sub><a href="paper">paper</a> · <a href="lean">Lean proof</a> · <a href="verify">code</a> · <a href="../">all results</a></sub></p>
<!-- visual:end -->

Sol LeWitt's *Incomplete Open Cubes* (1974) shows every set of edges of a cube that is connected, not contained in a plane, and not the whole cube, counted up to rotation with mirror images kept apart: there are 122. MathOverflow [question 508521](https://mathoverflow.net/q/508521) (Sam Hopkins, February 2026) asks for a quick argument for that number. The count had been checked by hand against LeWitt's list (Rozhkovskaya and Reb, 2015) and by computer, and Vejdemo-Johansson (arXiv:2602.20425) computed the analogous totals for all five Platonic solids.

**Theorem.** The incomplete open tetrahedra, cubes and octahedra number 6, 122 and 185. By number of edges `k = 3, …, 11`:

| | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | total |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| tetrahedron | 3 | 2 | 1 | | | | | | | 6 |
| cube | 3 | 5 | 14 | 24 | 32 | 25 | 13 | 5 | 1 | 122 |
| octahedron | 5 | 16 | 34 | 46 | 38 | 27 | 13 | 5 | 1 | 185 |

The totals are known. The note's contribution is a derivation of all three counts that can be checked with pencil and paper, and, as far as we know, the octahedron's row by number of edges. For many edges, Burnside's lemma counts all edge sets up to rotation, and only a few of them are disconnected. For few edges, delete the vertices the set does not use and count spanning trees of what is left, using one lemma: in a cycle with a hub, the spanning trees with a given set of spokes number the product of the arc lengths between the spokes.

Preprint v1, 11 October 2026, not peer reviewed. The finite counts are formally verified in Lean 4 (`lean/`, standard axioms only): the 24 rotations and their cycle types, the edge-set polynomial, the vertex bounds, every spanning-tree count and its fixed points under each stabiliser, and the sums. Burnside's lemma and the case analyses are in the paper and are checked exhaustively by the Python audits. The author used AI tools (OpenAI Codex for the first cube argument, Claude, Anthropic, for the rest), as described in the paper's acknowledgement, and is responsible for its content.

## Contents

- `paper/`: `note.tex` and `note.pdf`. `figs/` holds the TikZ figures written by `verify/fig_solids.py`.
- `verify/`:
  - `check_cube.py`: checks every intermediate count of the cube section: the classes by edge number, the vertex bounds, the five- and six-edge trees and their fixed points, the cyclic shapes, the four-edge classes and the disconnected sets with seven or more edges. It runs six mutants (identifying mirror images, keeping flat sets, requiring all eight vertices, keeping the full cube, 48 six-edge trees, no trees fixed by a third-turn), each of which must fail.
  - `check_octahedron_tetrahedron.py`: the same for the octahedron and tetrahedron sections, with six mutants.
  - `platonic_counts.py`: an independent direct enumeration of all edge sets of the cube and octahedron up to rotation, checked against the table. `MUTANT=1` identifies mirror images too and must fail.
  - `fig_solids.py`: the figures.
- `lean/`: a Lake project pinned to Lean 4.34.0 and Mathlib v4.34.0. `lean/README.md` maps the paper to Lean names, `CheckClaims.lean` prints their axioms, and `scripts/mutants.py` runs the mutation tests.

## Reproduce

```
cd verify && python3 check_cube.py && python3 check_octahedron_tetrahedron.py
python3 platonic_counts.py && MUTANT=1 python3 platonic_counts.py | tail -1
python3 fig_solids.py
cd ../paper && latexmk -pdf note.tex
cd ../lean && lake exe cache get && lake build LeanProofs && lake env lean CheckClaims.lean
```

## Licence

The paper is released under [CC BY 4.0](../LICENSE-PAPERS), the code under the [MIT licence](../LICENSE-CODE).
