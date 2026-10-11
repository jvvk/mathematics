# Cycles of length 2^n − 2 in the binary de Bruijn graph

<!-- visual:start -->
<p align="center"><img src="https://raw.githubusercontent.com/jvvk/jvvk/f1ea52db49392d1317df37b667d1b29c7edcb211/assets/debruijn-cycles-two-short.svg" width="760" alt="Cycles of length 2^n − 2 in the binary de Bruijn graph"></p>

<p align="center"><b>B(n) has (2ⁿ − (−1)ⁿ)/3 · 2^(2ⁿ⁻¹ − 2n + 2) cycles of length 2ⁿ − 2: a 1972 count, quoted since 1982 with only an outline and wrong as quoted on MathOverflow (4 instead of 3 for n = 3), now proved.</b><br><sub>Solved, with a correction · determinant algebra in Lean; BEST and matrix-tree theorems cited</sub></p>

<p align="center"><sub><a href="paper">paper</a> · <a href="lean">Lean proof</a> · <a href="verify">code</a> · <a href="../">all results</a></sub></p>
<!-- visual:end -->

A cycle of length `2^n − 2` in the binary de Bruijn graph `B(n)` is a circle of `2^n − 2` bits in which every
block of `n` consecutive bits appears at most once. A count of these cycles, attributed to Kibler (1972) in
Fredricksen's 1982 survey, has circulated with only an outline of a proof; as quoted on
[MathOverflow 227666](https://mathoverflow.net/q/227666) (Timothy Chow, 2016) it gives 4 for `n = 3`, where
there are 3.

**Theorem.** For `n ≥ 2`, `B(n)` has

```
T(n) = (2^n − (−1)^n)/3 · 2^(2^(n−1) − 2n + 2)
```

cycles of length `2^n − 2` (1, 3, 20, 2816, 88080384 for n = 2..6). The two missing vertices are either `0^n`
and `1^n`, giving the de Bruijn number `2^(2^(n−1) − n)`, or the two alternating strings, giving
`(2^(n−2) − (−1)^n)/3 · 2^(2^(n−1) − 2n + 2)`. The quoted expression is the second count with `n` replaced by
`n − 1`.

The second case is a rank-one change of the Laplacian of `B(n−1)`; the matrix determinant lemma needs one
inverse, and that inverse is a finite sum because a random walk on the de Bruijn graph is exactly uniform after
`n − 1` steps.

Preprint v1, 12 October 2026, not peer reviewed and not yet independently reviewed. The classification of the
two-edge deletions, the effect of each on the Laplacian, the exact mixing, the inverse, the determinant identity,
the return probabilities and the closed forms are formally verified in Lean 4 (`lean/`, standard axioms only);
the BEST theorem, the matrix-tree theorem and the de Bruijn count are cited. The author used AI tools (Claude,
Anthropic) in this work, as described in the paper's acknowledgement, and is responsible for its content.

## Contents

- `paper/`: `note.tex`, `note.pdf`, the figures `fig_b3.tex`, `fig_shift.tex` and their generator `make_fig.py`.
- `lean/`: a Lake project pinned to Lean 4.34.0 and Mathlib v4.34.0; `lean/README.md` maps results to Lean names,
  `CheckClaims.lean` prints their axioms, `scripts/mutants.py` runs 9 mutation tests.
- `verify/`:
  - `count.py`: direct enumeration of cycles for `n ≤ 5`, and both cases by exact determinants (Bareiss, root 0) for `n ≤ 11`.
  - `recheck/recheck.py`: an independent check sharing no code: Eulerian-trail enumeration of `B(n−1)` minus every pair of edges for `n ≤ 5`, its own exact elimination rooted at the last vertex for `n ≤ 11`, and the `n = 3` circles of the introduction; `--mutants` runs two mutants.

## Reproduce

```
cd verify
python3 -c "from count import check; check(11)"
python3 recheck/recheck.py && python3 recheck/recheck.py --mutants      # about six minutes
cd ../paper && latexmk -pdf note.tex
cd ../lean && lake exe cache get && lake build LeanProofs && lake env lean CheckClaims.lean
```

## Licence

The paper is released under [CC BY 4.0](../LICENSE-PAPERS), the code under the [MIT licence](../LICENSE-CODE).
