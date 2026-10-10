# Colour the points, not the plane

<!-- visual:start -->
<p align="center"><img src="https://raw.githubusercontent.com/jvvk/jvvk/ce98a02bacf5d0c8e5e47efa14a02c6eb671c9a1/assets/seven-colours.svg" width="760" alt="Colour the points, not the plane"></p>

<p align="center"><b>Points pairwise ≥ 1 apart contain N/7 pairwise more than √3 apart, but no tiling with seven colours proves it: every tiling scheme needs (1 + √3)² ≈ 7.46 colours, and nine half-open hexagon classes suffice.</b><br><sub>Answers a question · lemma, bound arithmetic and counterexample in Lean; eight colours open</sub></p>

<p align="center"><sub><a href="paper">paper</a> · <a href="lean">Lean proof</a> · <a href="verify">code</a> · <a href="../">all results</a></sub></p>
<!-- visual:end -->

If `N` points in the plane are pairwise at least `1` apart, at least `N/7` of them are pairwise more than `√3` apart. The accepted proof ([Mathematics Stack Exchange 1378338](https://math.stackexchange.com/q/1378338), Batominovski) colours the points greedily. Pedro asked ([question 1381502](https://math.stackexchange.com/q/1381502), unanswered) for a tiling proof instead: cells that cannot hold two points, coloured so that points in different cells of one colour are more than `√3` apart.

- **Theorem 1.** Every such tiling scheme uses at least `(1 + √3)² = 4 + 2√3 ≈ 7.46` colours, so at least eight. Thicken each cell of one colour by a disc of radius `√3/2`. The thickened cells are disjoint, and by the Brunn–Minkowski and isodiametric inequalities each cell fills at most `1/(1 + √3)²` of its thickened region.
- **Theorem 2.** Regular hexagons of side `1/2`, each owning three open edges and two vertices, coloured by the nine cosets of three times their lattice, form a scheme with nine colours. So a tiling proves `N/9`.
- **The 2023 hexagon answer fails.** Its seven-colour pattern puts `(0.45, 0)` and `(1.8, √3/4)` in hexagons of the same colour, about `1.418` apart.

So the answer to the tiling question is no for seven colours and yes for nine. Eight is open.

Preprint v1, 10 October 2026, not peer reviewed. The thirty-degree lemma, the arithmetic of Theorem 1 (the value of the density bound, its monotonicity, and `1/(1 + √3)² < 1/7`, hence eight colours) and the counterexample are formally verified in Lean 4 (`lean/`, standard axioms only). The Brunn–Minkowski and isodiametric inequalities are not in Mathlib and are quoted (Gardner, Bull. AMS 2002). The author used AI tools (Claude, Anthropic) in this work, as described in the paper's acknowledgement, and is responsible for its content.

## Contents

- `paper/`: `note.tex` and `note.pdf`. `figs/` holds the TikZ data written by `verify/fig_proof.py` and `verify/fig_hex.py`.
- `verify/`:
  - `seven_check.py`: checks the lemma on a fine grid and runs the greedy colouring on 300 random point sets. It computes the closest same-coloured hexagons in the seven-class pattern (`√7/2`) and in the nine-class pattern (exactly `√3`, across edges only), and checks the density bound. `MUTANT=1` (a `40°` lemma) and `MUTANT=2` (the bound `1/(1 + √3)`) must print `FAIL`.
  - `fig_proof.py`, `fig_hex.py`: Figures 1 and 2.
- `lean/`: a Lake project pinned to Lean 4.34.0 and Mathlib v4.34.0. `lean/README.md` maps results to Lean names, `CheckClaims.lean` prints their axioms, and `scripts/mutants.py` runs the mutation tests.

## Reproduce

```
cd verify && python3 seven_check.py && MUTANT=1 python3 seven_check.py | tail -1 && MUTANT=2 python3 seven_check.py | tail -1
python3 fig_proof.py && python3 fig_hex.py
cd ../paper && latexmk -pdf note.tex
cd ../lean && lake exe cache get && lake build LeanProofs && lake env lean CheckClaims.lean
```

## Licence

The paper is released under [CC BY 4.0](../LICENSE-PAPERS), the code under the [MIT licence](../LICENSE-CODE).
