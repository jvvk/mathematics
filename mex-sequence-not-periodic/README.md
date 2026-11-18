# A mex sequence that is not ultimately periodic

<!-- visual:start -->
<p align="center"><img src="https://raw.githubusercontent.com/jvvk/jvvk/c7403d6bbbc7106e1780d8c34833854afcb0116f/assets/mex.svg" width="760" alt="A mex sequence that never repeats"></p>

<p align="center"><b>Guy's question E27: the sequence from 1,1,1,0,1,0,1,1 is unbounded, so not ultimately periodic.</b><br><sub>Open problem settled · formally verified in Lean 4</sub></p>

<p align="center"><sub><a href="paper">paper</a> · <a href="lean">Lean proof</a> · <a href="verify">code</a> · <a href="../">all results</a></sub></p>
<!-- visual:end -->

Start with a few nonnegative integers and keep appending the least nonnegative integer that is not a sum `a_i + a_{n-i}` of two terms whose indices add up to the last index `n` already written. In Section E27 of *Unsolved Problems in Number Theory*, Guy asks whether every such mex sequence is ultimately periodic.

The answer is no. The mex sequence that starts `1,1,1,0,1,0,1,1` is unbounded (Theorem 1). Its zeros sit at the positions with remainder 0 or 3 modulo 5 (Lemma 1), and each zero copies an earlier value into the set whose least missing element is taken, so from the third block of five on, each new twin value differs from every earlier twin value (Lemma 2). Appendix A gives every term: from `n = 15` on, moving 15 positions ahead adds 4 at the positions with remainder 1 or 2 modulo 5 and 0 elsewhere. The answer concerns Guy's question with ordinary addition; the variant with addition without carries (OEIS A067018), closest to the games that motivate it, is untouched.

Preprint v3, 18 November 2026 (v1: 8 October; v2: 23 October), not peer reviewed. Zenodo: [doi:10.5281/zenodo.24352863](https://doi.org/10.5281/zenodo.24352863), identical to this folder at tag `mex-sequence-not-periodic-v3`. Lemmas 1 to 3 and Theorems 1 and 2 are formally verified in Lean 4 (`lean/`, standard axioms only); version 3 corrects points from an independent review by Codex (OpenAI); the author's own line-by-line reading of v3 is pending. The author used AI tools (Claude, Anthropic; Codex, OpenAI) in this work, as described in the paper's acknowledgement, and is responsible for its content.

**Version 3** (18 November 2026, tag `mex-sequence-not-periodic-v3`): corrections after an independent review. The abstract's summary of Lemma 2 is corrected (each new *twin* value is new; block 2 repeats the value 3); the superlinear-growth question is answered (`a_{n+1} ≤ ⌊n/2⌋ + 1`, since the pair sums are symmetric); the identification with greedy sum-free completions is stated for starting words that end in a zero and have a sum-free zero set; Horrocks and Nowakowski's *sapp regularity* is cited; verification wording matches the checks; implementation mutation suites supplement the Python negative controls and replace `mutants.sh`. Theorems unchanged.

**Version 2** (23 October 2026, tag `mex-sequence-not-periodic-v2`): expository revision of the paper (one sentence of the introduction reworded). The results, programs and Lean files are unchanged from v1.

## Contents

- `paper/`: `mex.tex`, `mex.pdf` and the figure `figs/fig_sequence.pdf`.
- `lean/`: a Lake project pinned to Lean 4.34.0 and Mathlib v4.34.0, about 550 lines. `lean/README.md` maps each result of the paper to its Lean name; `MexSequence/Audit.lean` prints the axioms of every one. `SOURCE-SNAPSHOT.json` records the development commit and the hash of every file. `scripts/mutants.toml` (run by `scripts/mutate.py`) plants ten wrong changes and checks that each stops the build, after a passing control build; `build-validation.log` and `mutation-validation.log` record the isolated build and the mutation run.
- `verify/`:
  - `verify_paper.py`: recomputes in exact arithmetic every number quoted in the paper except the search counts (those come from `search.py`); checks each step of the proofs of Lemmas 1 and 2 on every block within the first 3000 terms, and the conclusion of Lemma 3 (not each induction step); checks the growth bound of Section 5; ends with five negative controls (false statements that must fail against the correct data).
  - `mutants.toml` with `harness/mutate.py`: six implementation mutants (the mex, the pairing rule, the closed form three ways, the starting word), each of which must make the unchanged checks fail.
  - `search.py`: the search of Section 5 (every 0/1 starting word of length at most 8, 3000 terms each).
  - `make_fig.py`: draws Figure 1 into `paper/figs/fig_sequence.pdf` (the file the paper includes) and rechecks the closed form for the first 150 terms.

The remarks of Section 5 (zero sets and greedy sum-free sets, the search, the second example) are not formally verified; the second example is computational evidence only.

## Reproduce

```
cd verify
python3 -I verify_paper.py                 # every quoted number, seconds
python3 -I harness/mutate.py mutants.toml  # six implementation mutants, each rejected
python3 search.py                          # the search of Section 5, NumPy, seconds
python3 make_fig.py                        # Figure 1, matplotlib
cd ../paper && latexmk -pdf mex.tex
cd ../lean && lake exe cache get && lake build   # builds every module and prints the axiom audit
python3 -I scripts/mutate.py scripts/mutants.toml   # ten mutants, each rejected (then `lake build` again)
```

## Licence

The paper and figure are released under [CC BY 4.0](../LICENSE-PAPERS), the code under the [MIT licence](../LICENSE-CODE).
