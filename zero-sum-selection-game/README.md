# A zero-sum selection game on matrices

<!-- visual:start -->
<p align="center"><img src="https://raw.githubusercontent.com/jvvk/jvvk/c7403d6bbbc7106e1780d8c34833854afcb0116f/assets/zero-sum.svg" width="760" alt="A zero-sum selection game"></p>

<p align="center"><b>Lev's question: the winning matrices form a union of subspaces of dimension n(n+1)/2 − 1, and recognising them is Π₂ᵖ-complete.</b><br><sub>Open problem settled · verified by computation · partly in lean; reduction by hand</sub></p>

<p align="center"><sub><a href="paper">paper</a> · <a href="lean">Lean proof</a> · <a href="verify">code</a> · <a href="../">all results</a></sub></p>
<!-- visual:end -->

Two players play on a real `n × n` matrix. The Enemy selects `i` entries of row `i` for each `i`. Then You choose one selected entry in every row, and You win if your entries sum to zero. Vsevolod Lev asked on MathOverflow ([question 453809](https://mathoverflow.net/q/453809)) for a description of the winning matrices.

The paper proves three results:

- **Dimension (Theorem 1).** The winning matrices form a finite union of rational linear subspaces of dimension exactly `n(n+1)/2 − 1`. More generally, for rows of length `N_i` with quotas `k_i` the dimension is `Σ k_i − 1`. The proof is a short rank argument: delete positions one at a time and watch the span of the surviving zero-sum transversals shrink.
- **Order three (Theorem 2).** A `3 × 3` matrix is winning exactly when every first-row entry has two usable second-row positions. With distinct entries in every row, the winning matrices are five explicit families.
- **Complexity (Theorem 3).** Recognising winning integer matrices is `Π₂ᵖ`-complete, even with two values per row. So no polynomial-time test exists unless the polynomial hierarchy collapses.

Preprint v1, 9 October 2026, not peer reviewed.

- **Formally verified in Lean 4** (`lean/`, standard axioms only): the rank lemma and the dimension theorem for arbitrary row lengths and quotas; the order-three criterion; the collision lemma and the distinct-entry classification; the two-valued normal form behind the hardness proof.
- **Not formalised:**
  - the bookkeeping of the reduction (which rows are universal and which existential);
  - the twelve order-three families and the count of 1,107 components, which were computed and then rechecked independently;
  - the two remarks on further families.

The author used AI tools (Codex, OpenAI; Claude, Anthropic) in this work, as described in the paper's acknowledgement, and is responsible for its content.

## Contents

- `paper/`: `paper.tex` and `paper.pdf`.
- `lean/`: a Lake project pinned to Lean 4.34.0 and Mathlib v4.34.0; `lean/README.md` maps results to Lean names, `CheckClaims.lean` prints their axioms, `scripts/mutants.py` runs the mutation tests.
- `verify/`:
  - `recheck.py` is an independent check that plays the game literally and shares no code with the programs below or with the Lean. It checks:
    - the order-three criterion on all 592,704 matrices with sorted rows from `{−3, …, 3}`;
    - the five families against all matrices with distinct rows from `{−4, …, 4}`;
    - the 1,107 maximal winning subspaces (99, 576 and 432 of dimensions 5, 4, 3), by its own enumeration, together with their 12 orbits and which of them allow distinct entries;
    - the two-valued normal form on random matrices;
    - the reduction on random subset-sum instances, true and false;
    - the families of the remarks;
    - four mutants, which it rejects.

    `--quick` gives a short run; `recheck-full.log` is the full run.
  - `codex/` holds the programs that found the results:
    - `general_solver.py`, an exact solver for any order that returns an Enemy strategy for losing matrices;
    - `templates.py`, which enumerates the order-three components;
    - their own verification scripts and records.

## Reproduce

```
cd verify
python3 recheck.py --quick
cd ../paper && latexmk -pdf paper.tex
cd ../lean && lake exe cache get && lake build LeanProofs && lake env lean CheckClaims.lean
```

`recheck.py` uses only the Python standard library; the programs in `codex/` also use `sympy`.

## Licence

The paper is released under [CC BY 4.0](../LICENSE-PAPERS), the code under the [MIT licence](../LICENSE-CODE).
