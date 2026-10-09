# Six unit sticks and the diameter of a hexagon

<!-- visual:start -->
<p align="center"><img src="https://raw.githubusercontent.com/jvvk/jvvk/c7403d6bbbc7106e1780d8c34833854afcb0116f/assets/hexagon.svg" width="760" alt="Six matchsticks in a square"></p>

<p align="center"><b>No simple loop of six unit sticks fits in a unit square: the six-stick case of an open parity question.</b><br><sub>Partial progress on an open problem · partly in lean</sub></p>

<p align="center"><sub><a href="paper">paper</a> · <a href="lean">Lean proof</a> · <a href="verify">code</a> · <a href="../">all results</a></sub></p>
<!-- visual:end -->

Join six sticks of length one, end to end, into a closed loop that does not cross itself. JetfiRex asked on MathOverflow ([question 481323](https://mathoverflow.net/q/481323)) and Mathematics Stack Exchange ([question 4987974](https://math.stackexchange.com/q/4987974)) whether every simple unit polygon in the closed unit square, other than the square itself, must have an odd number of sides. Pentagons and heptagons fit; even numbers seem not to.

Every simple unit hexagon has diameter greater than `√2`, the constant is sharp, and it is never attained (Theorem 1). So no simple unit hexagon fits in a closed unit square or a closed disk of radius `1/√2`, while one fits in any larger square or disk (Corollary 1). This settles the six-sided case of the question. For octagons, the two-reflex case is reduced to a single configuration (Proposition 2); eight or more sides remain open.

Preprint v1, 9 October 2026, not peer reviewed. The lemmas, the triangle proposition, the angle counting, the sign lemmas of the case analysis and every claim about the sharpness family are formally verified in Lean 4 (`lean/`, standard axioms only). The Jordan-curve facts about hull pockets and the passage from a polygon to these configurations are checked by hand; `lean/README.md` lists exactly what is and is not formalised. The author used AI tools (Codex, OpenAI; Claude, Anthropic) in this work, as described in the paper's acknowledgement, and is responsible for its content.

## Contents

- `paper/`: `note.tex` and `note.pdf`.
- `lean/`: a Lake project pinned to Lean 4.34.0 and Mathlib v4.34.0; `lean/README.md` maps results to Lean names, `CheckClaims.lean` prints their axioms, `scripts/mutants.py` runs the mutation tests.
- `verify/`:
  - `verify.py` and `manuscript_checks.py` (with `algebraic_search.py`): exact local checks of individual lemma statements (SymPy identities, Z3 `QF_NRA` negations) and of the sharpness family at five parameters, with controls.
  - `recheck/recheck.py`: an independent recheck sharing no code with the programs above: symbolic identities of Lemmas 1 and 3 and of the sign identity, exact algebraic checks of the sharpness family at seven parameters, sweeps, and a numerical minimisation of the diameter over simple unit hexagons (evidence only). `--quick` for a short run.
  - `explore/`: numerical and grid searches (`min_diameter.py` for n = 5, 7, 8) and the global solver queries, which returned `unknown`. Exploratory, not proofs.

## Reproduce

```
cd verify
python3 recheck/recheck.py --quick     # about a minute; drop --quick for the full minimisation
python3 verify.py && python3 manuscript_checks.py
cd ../paper && latexmk -pdf note.tex
cd ../lean && lake exe cache get && lake build LeanProofs && lake env lean CheckClaims.lean
```

Python needs `numpy`, `scipy`, `sympy` and `z3-solver` (`shapely` for two exploration scripts).

## Licence

The paper is released under [CC BY 4.0](../LICENSE-PAPERS), the code under the [MIT licence](../LICENSE-CODE).
