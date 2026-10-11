# The cells of a regular polygon are small

<!-- visual:start -->
<p align="center"><img src="https://raw.githubusercontent.com/jvvk/jvvk/0bc67cde38b98aaeda75fe7c7ddebe8c770713f6/assets/polygon-cells-are-small.svg" width="760" alt="The cells of a regular polygon are small"></p>

<p align="center"><b>Draw every diagonal of a regular n-gon with side 1: every cell has area at most C/n, except the odd central cell (area → π/16); the side triangles are usually not the largest.</b><br><sub>Partial answer to a question · arithmetic core in Lean</sub></p>

<p align="center"><sub><a href="paper">paper</a> · <a href="lean">Lean proof</a> · <a href="verify">code</a> · <a href="../">all results</a></sub></p>
<!-- visual:end -->

Draw every diagonal of a regular `n`-gon with side 1. How large can a cell be? MathOverflow [question 436753](https://mathoverflow.net/q/436753) (and its twin on Mathematics Stack Exchange, [4593337](https://math.stackexchange.com/q/4593337)) asks for bounds on the largest cell and, failing sharp bounds, whether `n` times the largest area stays bounded.

**Theorem.** There is an absolute constant `C` such that every cell has area at most `C/n`, except the central cell when `n` is odd.

**Proposition.** For odd `n` the central cell is a regular `n`-gon of inradius `1/(4 cos(π/2n))`; its area tends to `π/16`, so the exception is necessary.

**Observation (certified).** The side triangles, of area `(1/4) tan(π/n)`, give the right order but are usually not the largest cells: for every `n` from 9 to 60 except 10, 18, 28, 34 and 57, some cell is strictly larger, certified in ball arithmetic. For `9 ≤ n ≤ 60`, `n` times the largest ordinary area lies between 0.78 and 1.39.

The proof traps each cell between diagonals in two independent directions. The diagonals through a point `x` form a curve in the plane of (normal angle, offset), and the actual diagonals form a lattice; lattice points on a line of slope `a/b` tangent to that curve give diagonals passing on both sides of `x` and close to it. Near the rim the vertex fans finish the job, and near the centre a packing argument with the rotated copies of a cell. The sharp constant is open.

Preprint v1, 11 October 2026, not peer reviewed. An independent referee read found no gap. The arithmetic core is formally verified in Lean 4 (`lean/`, standard axioms only): the parity lattice of chords along a rational tangent, the coprimality behind it, and the trigonometric facts about the odd central cell. The geometric and analytic estimates are proved in the paper and not formalised. The author used AI tools (OpenAI Codex and Claude, Anthropic), as stated in the paper, and is responsible for its content.

## Contents

- `paper/`: `note.tex` and `note.pdf`; `figs/` holds the TikZ figures written by `verify/fig_cells.py`.
- `verify/`:
  - `largest_cell.py`: the certified comparison of Observation 3 (shapely for the arrangement, python-flint ball arithmetic for the certificate). `MUTANT=1` (no shrinking) and `MUTANT=2` (twice the side triangle) must fail.
  - `verify.py`, `run_checks.py`: a floating-point audit of the finite ingredients of the rational-tangent lemma (5841 assertions), with seven planted errors and an always-passing verifier rejected. Illustration, not proof.
  - `fig_cells.py`: the figures.
- `lean/`: a Lake project pinned to Lean 4.34.0 and Mathlib v4.34.0. `lean/README.md` maps the paper to Lean names, `CheckClaims.lean` prints their axioms, and `scripts/mutants.py` runs the mutation tests.

## Reproduce

```
cd verify && python3 largest_cell.py && MUTANT=1 python3 largest_cell.py 9; MUTANT=2 python3 largest_cell.py
python3 run_checks.py
python3 fig_cells.py
cd ../paper && latexmk -pdf note.tex
cd ../lean && lake exe cache get && lake build LeanProofs && lake env lean CheckClaims.lean
```

`largest_cell.py` needs `shapely` and `python-flint`; `largest_cell.py 9 10 ... 60` reproduces the full range.

## Licence

The paper is released under [CC BY 4.0](../LICENSE-PAPERS), the code under the [MIT licence](../LICENSE-CODE).
