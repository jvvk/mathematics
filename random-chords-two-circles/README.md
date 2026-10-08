# Random chords of two circles and a third centre

Three circles touch in a row with radii `a`, `b`, `c` in geometric progression. Choose `A` uniformly on the first circle and `B`, `C` uniformly on the second. Dan observed numerically, and asked on MathOverflow (question 499477) why, that the lines `AB` and `BC` meet the third circle with the same probability.

The paper explains it through a fact about two circles. For independent uniform points `A`, `B` on two circles whose discs have disjoint interiors, the signed offsets of the line `AB` from the two centres, each divided by its radius, are independent with the arcsine law (Lemma 2). The proof is a change of variables over the four pairs of points on a line, whose contributions add to a constant because the half-chords cancel. From this, Theorem 4 decides exactly which points `O` on the line of centres see `AB` and the chord `BC` at the same distance in distribution: `O` is the second centre, or the circles touch and `|QO| = b(a + b)/a`. This answers Dan's question for every ratio, extends it to every circle about the third centre and to chains of circles, shows that the progression is necessary, and gives a single integral for the common hit probability.

Preprint v1, 8 October 2026, not peer reviewed. Every proved result of the paper is also formally verified in Lean 4 (`lean/`, standard axioms only). The exposition has not yet been independently reviewed. The author used AI tools (Claude, Anthropic; Codex, OpenAI) in this work, as described in the paper's acknowledgements, and is responsible for its content.

## Contents

- `paper/`: `paper.tex`, `paper.pdf`, the two figures and the scripts that draw them.
- `verify/`: three checkers and `run_all.py` (`README.md` lists what each checks). They check the change-of-variables calculation, the weight comparison and centre classification, the off-axis second-moment identity and the hit-probability integrals, in exact rational arithmetic where possible; nine deliberately false variants must each fail.
- `lean/`: a Lake project pinned to Lean 4.34.0 and Mathlib v4.34.0. `lean/README.md` maps each result of the paper to its Lean name; `RandomChords/Audit.lean` prints the axioms of every one. `SOURCE-SNAPSHOT.json` records the development commit and the hash of every file. `mutants.sh` plants 23 wrong changes and checks that each fails to build. Not formalised: the numerical value in Corollary 8 and its agreement with Dan's dilogarithm expression (both computed in `verify/`), and Santaló's formula, which the paper cites in a remark but does not use.

## Reproduce

```
cd verify
python3 run_all.py                      # needs numpy and mpmath; under a minute
cd ../paper && latexmk -pdf paper.tex
cd ../lean && lake exe cache get && lake build   # builds every module and prints the axiom audit
./mutants.sh                                     # 23 mutants, each rejected
```

## Licence

The paper is released under [CC BY 4.0](../LICENSE-PAPERS), the code under the [MIT licence](../LICENSE-CODE).
