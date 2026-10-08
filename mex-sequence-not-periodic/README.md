# A mex sequence that is not ultimately periodic

Start with a few nonnegative integers and keep appending the least nonnegative integer that is not a sum `a_i + a_{n-i}` of two terms whose indices add up to the last index `n` already written. In Section E27 of *Unsolved Problems in Number Theory*, Guy asks whether every such mex sequence is ultimately periodic.

The answer is no. The mex sequence that starts `1,1,1,0,1,0,1,1` is unbounded (Theorem 1). Its zeros sit at the positions with remainder 0 or 3 modulo 5 (Lemma 1), and each zero copies an earlier value into the set whose least missing element is taken, so from the third block of five on, each block brings a value no earlier block had (Lemma 2). Appendix A gives every term: from `n = 15` on, moving 15 positions ahead adds 4 at the positions with remainder 1 or 2 modulo 5 and 0 elsewhere. The answer concerns Guy's question with ordinary addition; the variant with addition without carries (OEIS A067018), closest to the games that motivate it, is untouched.

Preprint v1, 8 October 2026, not peer reviewed. Lemmas 1 to 3 and Theorems 1 and 2 are formally verified in Lean 4 (`lean/`, standard axioms only); the exposition has not yet been independently reviewed. The author used AI tools (Claude, Anthropic; Codex, OpenAI) in this work, as described in the paper's acknowledgement, and is responsible for its content.

## Contents

- `paper/`: `mex.tex`, `mex.pdf` and the figure `figs/fig_sequence.pdf`.
- `lean/`: a Lake project pinned to Lean 4.34.0 and Mathlib v4.34.0, about 550 lines. `lean/README.md` maps each result of the paper to its Lean name; `MexSequence/Audit.lean` prints the axioms of every one. `SOURCE-SNAPSHOT.json` records the development commit and the hash of every file. `mutants.sh` plants ten wrong changes and checks that each fails to compile.
- `verify/`:
  - `verify_paper.py`: recomputes in exact arithmetic every number quoted in the paper, checks each step of the proofs of Lemmas 1 to 3 on the first 3000 terms, and kills five planted mutants.
  - `search.py`: the search of Section 5 (every 0/1 starting word of length at most 8, 3000 terms each).
  - `make_fig.py`: draws Figure 1 and rechecks the closed form for the first 150 terms.

The remarks of Section 5 (zero sets and greedy sum-free sets, the search, the second example) are not formally verified; the second example is computational evidence only.

## Reproduce

```
cd verify
python3 verify_paper.py                    # every quoted number, seconds
python3 search.py                          # the search of Section 5, NumPy, seconds
python3 make_fig.py                        # Figure 1, matplotlib
cd ../paper && latexmk -pdf mex.tex
cd ../lean && lake exe cache get && lake build   # builds every module and prints the axiom audit
./mutants.sh                                     # ten mutants, each rejected
```

## Licence

The paper and figure are released under [CC BY 4.0](../LICENSE-PAPERS), the code under the [MIT licence](../LICENSE-CODE).
