# Remoteness minimisers with three branch vertices: a counterexample to Conjecture 4.4 of Allie, du Preez, Hefty and Mafunda

<!-- visual:start -->
<p align="center"><img src="visual.svg" width="760" alt="The tree T: segments 53 and 23 in a row, three 9s at the left end, a 21 at the middle junction, six 1s at the right end"></p>

<p align="center"><b>For the segment sequence (53, 23, 21, 9, 9, 9, 1⁶), every tree of minimum remoteness has three branch vertices, so the conjectured bound of two fails.</b><br><sub>Conjecture disproved · comparison with every starlike and two-branch tree verified in Lean 4 · minimality over all trees by two independent programs</sub></p>

<p align="center"><sub><a href="paper">paper</a> · <a href="lean">Lean proof</a> · <a href="verify">code</a> · <a href="../">all results</a></sub></p>
<!-- visual:end -->

The remoteness of a tree is the largest average distance from a vertex to all the others. A segment is a maximal path whose inner vertices have degree 2, and the lengths of the segments form the tree's segment sequence. Allie, du Preez, Hefty and Mafunda ([arXiv:2611.27685](https://arxiv.org/abs/2611.27685), 20 November 2026, Conjecture 4.4) conjectured that among all trees with a given segment sequence, one of minimum remoteness is starlike or has exactly two branch vertices.

This note proves:

- **Theorem 1.2.** For `D = (53, 23, 21, 9, 9, 9, 1, 1, 1, 1, 1, 1)`, and for `sD` for every integer `s ≥ 1`, every `D`-tree of minimum remoteness has exactly three branch vertices. The tree `T` in the picture has maximum transmission 5962; every starlike or two-branch `D`-tree has at least 5971.
- **Theorem 1.3.** For every segment sequence `(L, p, h, ..., h)`, the shape the authors named as the likeliest source of a counterexample, the conjecture holds.

The obstruction is a subset sum: a two-branch tree would have to put short segments of total 25 or 26 on one side, and no subset of `{9, 9, 9, 1, 1, 1, 1, 1, 1}` has either total.

Preprint v1, 23 November 2026, not peer reviewed; released before the author's line-by-line reading. Zenodo: [doi:10.5281/zenodo.24483605](https://doi.org/10.5281/zenodo.24483605), identical to this folder at tag `remoteness-three-branch-trees-v1`. The author used AI tools (Claude, Anthropic; Codex, OpenAI) in this work, as the paper's Section 5 describes, and is responsible for its content.

## Contents

- `paper/`: `remoteness.tex` and `remoteness.pdf`.
- `verify/` (Python 3 with NumPy and networkx). Each program exits nonzero if its results differ from the paper's values.
  - `verify_exhaustive.py`: builds `T`, the starlike tree and every two-branch `D`-tree explicitly and runs breadth-first search from every vertex (5962, 6160, 5971). Output `verify_k12.out`.
  - `true_min.py` (with `remote.py`): every series-reduced tree with 12 edges and every distinct assignment of `D`; the minimum by number of branch vertices (Proposition 3.3). Output `true_min_k12.out`.
  - `recheck_table.py`: the same table by a separately written program sharing no code (skeletons from networkx, values from explicit paths). Output `recheck_table.out`.
  - `searches/`: the exhaustive searches of Remark 3.5, with their logs (`searches/README.md`).
- `lean/`: a Lean 4 project pinned to the Mathlib version it was checked with; `lean/README.md` lists what is formalised and what is not.

## Reproduce

```
cd verify
python3 verify_exhaustive.py '[[0,1,53],[1,2,23]]' '{"0":[9,9,9],"1":[21],"2":[1,1,1,1,1,1]}'
python3 true_min.py 53 23 21 9 9 9 1 1 1 1 1 1
python3 recheck_table.py 53 23 21 9 9 9 1 1 1 1 1 1
cd ../lean && lake exe cache get && lake build && lake env lean CheckClaims.lean
cd ../paper && latexmk -pdf remoteness.tex
```

The programs take under a minute each. The Lean mutation suite: `cd lean/scripts && python3 mutate.py mutants.toml` (about 15 minutes).

## Licence

The paper is released under [CC BY 4.0](../LICENSE-PAPERS), the code under the [MIT licence](../LICENSE-CODE).
