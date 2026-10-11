# Every number except three is the path count of a best-connected pair

<!-- visual:start -->
<p align="center"><img src="https://raw.githubusercontent.com/jvvk/jvvk/f1ea52db49392d1317df37b667d1b29c7edcb211/assets/every-path-count-but-three.svg" width="760" alt="Every number except three is the path count of a best-connected pair"></p>

<p align="center"><b>The largest number of simple paths between two vertices of a graph takes every positive integer value except 3.</b><br><sub>Solved · construction in Lean; the impossibility of 3 by hand</sub></p>

<p align="center"><sub><a href="paper">paper</a> · <a href="lean">Lean proof</a> · <a href="verify">code</a> · <a href="../">all results</a></sub></p>
<!-- visual:end -->

For a graph `G` let `f(G)` be the largest number of simple paths between two distinct vertices. Trees give 1,
cycles 2, `K_{2,3}` gives 4 and `K_4` gives 5; no graph gives 3, a fact behind a task at IOI 2020. Which other
values are impossible ([MathOverflow 371851](https://mathoverflow.net/q/371851), Mikhail Tikhomirov, 2020)?

**Theorem.** Every positive integer except 3 is `f(G)` for some graph `G`.

Add `a` new vertices to a small graph `H`, each joined to the same two vertices `x` and `y`. A simple path meets
`x` and `y` once each, so it uses at most one new vertex on the way, and every pair's count is a straight line in
`a`. Four choices of `H` give `f = 2a, 6a + 1, 6a + 9, 6a + 11` for every `a ≥ 1`; with `K_2`, `K_4`, the wheel
`W_4` and one graph on six vertices (for 11) this covers every `k ≠ 3`. The impossibility of 3 is proved in the
note by a short block-and-theta argument.

Preprint v1, 12 October 2026, not peer reviewed and not yet independently reviewed. The construction (path
generator proved exact, transfer of paths along embeddings, at most one interior new vertex, the affine count
`N_b + (a − b)T`, the four families for every `a`, the small graphs, and the final theorem for simple graphs) is
formally verified in Lean 4 (`lean/`, standard axioms only); the impossibility of 3 is proved by hand and not
formalised. The author used AI tools (Claude, Anthropic) in this work, as described in the paper's
acknowledgement, and is responsible for its content.

## Contents

- `paper/`: `note.tex`, `note.pdf`, the figure `fig_family.tex` and its generator `make_fig.py`.
- `lean/`: a Lake project pinned to Lean 4.34.0 and Mathlib v4.34.0; `lean/README.md` maps results to Lean names,
  `CheckClaims.lean` prints their axioms, `scripts/mutants.py` runs 10 mutation tests.
- `verify/` (needs `networkx`):
  - `paths.py`, `family.py`, `verify.py`: all-pairs path counts, the families `G_a`, and the exact check that `f(G_a) = sa + r` for every `a ≥ 1` (lines read at `a = 2, 3, 4`, brute force for `a ≤ 9`); `mutants.py` runs six mutants.
  - `family2.py`, `family3.py`: the searches over bases `H` with at most seven vertices behind the families and the negative remark (no slope-2 odd family, no `4a + 1` family).
  - `recheck/mo_check.py`: an independent plain-Python check (own path counter, own reading of the lines), the same code as in the MathOverflow answer; `recheck/mutants.py` runs three mutants.

## Reproduce

```
cd verify
python3 verify.py && python3 mutants.py
python3 recheck/mo_check.py && python3 recheck/mutants.py
cd ../paper && latexmk -pdf note.tex
cd ../lean && lake exe cache get && lake build LeanProofs && lake env lean CheckClaims.lean
```

## Licence

The paper is released under [CC BY 4.0](../LICENSE-PAPERS), the code under the [MIT licence](../LICENSE-CODE).
