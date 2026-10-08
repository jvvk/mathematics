# Tiling almost-squares with smaller distinct almost-squares

An almost-square is a `k × (k+1)` rectangle. Erich Friedman asked for which `n` the `n × (n+1)` almost-square can be cut into almost-squares of distinct sizes, all smaller than `n` (Math Magic, Problem of the Month, May 2012), and conjectured that every `n ≥ 20` works.

The answer: exactly when `n ∈ {4, 10, 12, 14, 15, 18}` or `n ≥ 20` (Theorem 1). The construction scales a perfect squared square and moves each cut line by an integer so that every square becomes an almost-square; one counting identity proves it correct and gives a parity lemma explaining why the squared square of side 112 reaches only even `n` and the one of side 110 only odd `n`. Explicit tilings cover the remaining `n` from 20 to 248, and an exhaustive search settles `n ≤ 19`.

Preprint v1, 8 October 2026, not peer reviewed; the exposition has not yet been independently reviewed. Friedman's list of solved problems credits the result. The author used an AI tool (Claude, Anthropic) in this work, as described in the paper's acknowledgements, and is responsible for its content.

## Contents

- `paper/`: `almost.tex`, `almost.pdf` and the figure sources `fig_*.tex`.
- `verify/`: every finite check behind the theorem. `sh reproduce.sh` reruns them all: `verify/audit.py` (a checker sharing no code with the programs that found the tilings) checks every explicit tiling cell by cell, every inflation and the conditions of Lemma 4, and the coverage of `20 ≤ n ≤ 20000`; `src/frame.c` is the exhaustive search for `n ≤ 19` and `verify/small_sat.py` a second, independent one (z3). `out/` holds the squared squares, the 128 inflation classes, the 151 explicit tilings and the six small ones; `SHA256SUMS` their checksums. `src/fill.py` and `verify/base_reach.py` are the z3 searches that produced the fixed-scale tilings (`out/reach`).
- `lean/`: a Lake project pinned to Lean 4.34.0 and Mathlib v4.34.0, about 2,650 lines, formalising Theorem 1 (for real rectangles and for unit cells), every lemma, and every number printed in the paper. `lean/README.md` maps each result to its Lean name; `AlmostSquares/Audit.lean` prints the axioms. **Trust note:** the impossibility for `n = 16, 17, 19` is checked with `native_decide`, which relies on Lean's compiler as well as its kernel (one auxiliary axiom per case, `AlmostSq.noTiling_16._native.native_decide.ax_1_1` and likewise for 17 and 19, printed by the audit), because the kernel run needs more memory than a laptop has; these three cases are also settled by the two independent searches in `verify/`. Everything else is kernel-checked with the standard axioms. `mutants.sh` plants 28 wrong changes and checks that each fails. `SOURCE-SNAPSHOT.json` records the development commit and the hash of every file. The paper itself does not describe the formalisation.

## Reproduce

```
cd verify && sh reproduce.sh               # every finite check; needs python3 and a C compiler (z3 optional)
cd ../paper && latexmk -pdf almost.tex
cd ../lean && lake exe cache get && lake build && ./mutants.sh
```

## Licence

The paper and figures are released under [CC BY 4.0](../LICENSE-PAPERS), the code under the [MIT licence](../LICENSE-CODE).
