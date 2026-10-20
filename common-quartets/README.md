# Common quartets of several phylogenetic trees

<!-- visual:start -->
<p align="center"><img src="https://raw.githubusercontent.com/jvvk/jvvk/0878da07ac387e6537e9490078e189c75b7b8415/assets/quartets.svg" width="760" alt="Common quartets of several phylogenetic trees"></p>

<p align="center"><b>Any three phylogenetic trees on 14 species agree on some four-species subtree, and 13 is not enough: h(3) = 14. For k trees, 2ᵏ + 2 ≤ h(k) ≤ 2·3ᵏ⁻¹ + 1, replacing a four-times iterated exponential.</b><br><sub>Question answered · bounds and the 13-leaf example in Lean; h(3) ≤ 14 also by checked SAT proofs</sub></p>

<p align="center"><sub><a href="paper">paper</a> · <a href="lean">Lean proof</a> · <a href="verify">code</a> · <a href="../">all results</a></sub></p>
<!-- visual:end -->

Let `h(k)` be the least `n` such that any `k` unrooted binary phylogenetic trees on the same `n` leaves display a common quartet. Snir and Yuster ([DAM 387 (2026)](https://doi.org/10.1016/j.dam.2026.02.042), §5) asked for its value. It was known that `h(2) = 6` and `11 ≤ h(3) ≤ 14`, and the best published upper bound for general `k` (Currie, Czabarka, Fischer, Simmons, Székely and Wicke, [arXiv:2607.12778](https://arxiv.org/abs/2607.12778)) was a four-times iterated exponential.

This note proves:

- **Theorem 1.1.** `h(3) = 14`. The lower bound is three trees `T`, `3T`, `9T` on `ℤ₁₃` with no common quartet. The upper bound is Snir and Yuster's, whose error-free form is proved there in outline; it is confirmed here independently by an exhaustive SAT search over the 135 shapes of the first tree, each unsatisfiable instance carrying an LRAT proof accepted by `lrat-check`.
- **Theorem 1.2.** `2ᵏ + 2 ≤ h(k) ≤ 2·3ᵏ⁻¹ + 1` for every `k ≥ 2`. The upper bound applies to trees the iteration that Asplund, Do, Hamm, Székely, Taylor and Wang used for `k`-planar crossing numbers. The lower bound is Snir and Yuster's `h*(k) = 2ᵏ + 2` for caterpillars; the note writes out an explicit family of `k` caterpillars on `2ᵏ + 1` leaves, which they omitted, with a proof.
- **Theorem 1.3.** `22 ≤ h(4) ≤ 55`, and `h(4) ≤ 41` given the error-free form of Snir and Yuster's Theorem 1.3.
- **Proposition 5.2.** Up to the symmetries of the form `T, 3T, 9T`, there are exactly six 13-leaf examples (19,440 trees).

Preprint v1, 20 October 2026, not peer reviewed. The bound `h(k) ≤ 2·3ᵏ⁻¹ + 1` (with trees abstracted to split systems, see `lean/README.md`), the caterpillar family for every `k`, and both 13-leaf examples are formally verified in Lean 4 (`lean/`, standard axioms only). The author used an AI tool (Claude, Anthropic) in this work, as described in the paper's declaration, and is responsible for its content.

## Contents

- `paper/`: `common-quartets.tex` and `common-quartets.pdf`.
- `verify/` (Python 3 with [PySAT](https://pysathq.github.io/), `pip install python-sat`):
  - `recheck_paper.py`: an independent recheck of every finite claim, sharing no code with the rest of `verify/`; it parses the Newick strings from the `.tex`. Checks Proposition 5.1 (715 quartets), the 21-leaf example for `k = 4` (5985 quartets), `F_k` for `k ≤ 6`, the `k = 3` table and Snir and Yuster's example, the tree `T′` and its involution, and Proposition 6.2 on `ℤ₄₀`. About 2 seconds.
  - `run_all.py`: the fast checks of the search code: Snir and Yuster's Figure 4, the 13-leaf witness, the SAT encoding (it counts 15, 105 and 945 trees on 5, 6, 7 leaves), `n = 13` satisfiable and shape 0 at `n = 14` unsatisfiable. About 35 seconds. `mutants.py` plants 8 errors in these scripts; each must make `run_all.py` fail.
  - `sat_h3.py`, `shapes.py`, `shapes_indep.py`, `by_shape.py`, `certify.py`: the `n = 14` proof. `certify.py` regenerates and checks the 135 LRAT proofs (about 5,500 s of solver time and 32.6 GB of proofs, each deleted after checking); it needs CaDiCaL 2.1.3 and `lrat-check` from drat-trim, located by the environment variables `CADICAL` and `LRATCHECK`. `n14_lrat.jsonl` and `n14_shapes.jsonl` are the logs of the run.
  - `frob.py`, `certify_frob.py`, `cyclic.py`, `cyclic1.py`, `classes13.py`, `recount13.py`, `explore13.py`, `witness13_cyclic.py`, `witness21_k4.py`: the one-tree symmetric encoding, the classification behind Proposition 5.2 and its independent recount, and the searches of Section 6; the `.log` and `.jsonl` files are their outputs.
  - `catfamily.py`, `caterpillar.py`, `reflect.py`, `iterate.py`, `quartets.py`, `decode.py`: the caterpillar family checked to `k = 7`, the iteration run as an algorithm, and shared helpers.
- `lean/`: a Lake project pinned to Lean 4.34.0 and Mathlib v4.34.0; `lean/README.md` maps results to Lean names, `CheckClaims.lean` prints their axioms, `scripts/mutants.py` runs the 17 mutation tests.

## Reproduce

```
cd verify && python3 recheck_paper.py && python3 run_all.py && python3 mutants.py | tail -1
cd ../paper && latexmk -pdf common-quartets.tex
cd ../lean && lake exe cache get && lake build LeanProofs && lake env lean CheckClaims.lean
```

The full `n = 14` certification is `python3 verify/certify.py --tmp <dir with ~40 GB free> --log n14_rerun.jsonl` (about 5,500 s of solver time; CaDiCaL and lrat-check installed).

## Licence

The paper is released under [CC BY 4.0](../LICENSE-PAPERS), the code under the [MIT licence](../LICENSE-CODE).
