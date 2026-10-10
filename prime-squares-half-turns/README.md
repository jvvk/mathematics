# Prime squares and half-turns

<!-- visual:start -->
<p align="center"><img src="https://raw.githubusercontent.com/jvvk/jvvk/c9d3ddf9521a979a783ef5845555fa4222272054/assets/prime-squares.svg" width="760" alt="Prime squares and half-turns"></p>

<p align="center"><b>A p × p square, p prime, cut into p congruent pieces that are only translated or half-turned must be cut into bars; with quarter-turns too, the question is open.</b><br><sub>Partial progress · algebra formally verified in Lean · full question open</sub></p>

<p align="center"><sub><a href="paper">paper</a> · <a href="lean">Lean proof</a> · <a href="verify">code</a> · <a href="../">all results</a></sub></p>
<!-- visual:end -->

JetfiRex asked on MathOverflow ([question 487157](https://mathoverflow.net/q/487157)) and Mathematics Stack Exchange ([question 5007342](https://math.stackexchange.com/q/5007342)) whether a `p × p` square, `p` prime, can be cut into `p` congruent `p`-ominoes in any way other than into `p` straight bars. Composite sizes have other tilings (an exhaustive search finds them for every composite `n ≤ 14`), so any proof must use primality. The question is a discrete case of Danzer's open conjecture on cutting a square into congruent pieces.

The note proves two restricted forms, without assuming the piece is connected:

- **Theorem 1.** For every prime `p`, if each piece is a translate of one cell set `P` or of its half-turn, then `P` is a straight bar.
- **Theorem 2.** For odd `p`, the same holds with the half-turn replaced by any one fixed reflection of the square. (For `p = 2` it fails: two diagonal cells and their mirror image tile the `2 × 2` square.)

The proof encodes cells as Laurent monomials, so a tiling becomes `F·U + F*·V = Q_p(x) Q_p(y)` with `F*` the half-turn of the piece. Either `F` and `F*` share a factor, which must be one of the two cyclotomic primes of the board and forces a bar, or they are coprime, and evaluating `F ∣ U* − V` at `(1,1)` shows that only one orientation is used. With translations alone the result is close to known theorems (Szegedy; Horak and Kim) and is not claimed as new; `p = 3` follows from Maltby's classification of trisected rectangles. Quarter-turns, or two different reflections, bring in a third tile polynomial and the argument stops: the full question is open.

Preprint v1, 10 October 2026, not peer reviewed and not yet independently reviewed. The algebraic core is formally verified in Lean 4 (`lean/`, standard axioms only); the unique factorisation of the Laurent ring and the encoding of a tiling are quoted. The author used AI tools (Claude, Anthropic) in this work, as described in the paper's acknowledgement, and is responsible for its content.

## Contents

- `paper/`: `note.tex`, `note.pdf` and the figure sources `fig_*.tex`.
- `lean/`: a Lake project pinned to Lean 4.34.0 and Mathlib v4.34.0; `lean/README.md` maps results to Lean names, `CheckClaims.lean` prints their axioms, `scripts/mutants.py` runs 9 mutation tests.
- `verify/`:
  - `tilesq.c`: exhaustive search for `n ≤ 14`, every free `n`-omino in all eight orientations; `check.py` compiles it, asserts every number the note quotes (free counts against OEIS A000105, the composite counts, only bars for primes), runs a translations-only control and rejects five mutants.
  - `verify.py` and `run_checks.py`: 1,087 exact assertions on the ingredients of the proof (cell images and substitutions, the factor obstruction, quotients, orientation counts, a composite control) and six deliberate mutations, all rejected.
  - `recheck/recheck.py`: an independent check sharing no code with the rest: every `p`-cell set for `p = 3, 5` (connected or not) and every heptomino, with the half-turn and each reflection, tiles only as bars; the `p = 2` and `n = 4` controls; three mutants of its own. `recheck-full.log` is the full run.

## Reproduce

```
cd verify
python3 check.py              # about 10 s
python3 run_checks.py         # needs SymPy
python3 recheck/recheck.py    # about 5 s
cd ../paper && latexmk -pdf note.tex
cd ../lean && lake exe cache get && lake build LeanProofs && lake env lean CheckClaims.lean
```

## Licence

The paper is released under [CC BY 4.0](../LICENSE-PAPERS), the code under the [MIT licence](../LICENSE-CODE).
