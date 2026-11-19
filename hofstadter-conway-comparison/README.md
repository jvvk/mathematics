# A comparison theorem for the Hofstadter–Conway $10,000 sequence and its alternating variant

<!-- visual:start -->
<p align="center"><img src="https://raw.githubusercontent.com/jvvk/jvvk/c7403d6bbbc7106e1780d8c34833854afcb0116f/assets/conway.svg" width="760" alt="Newman-Conway and its cousin"></p>

<p align="center"><b>Alkan's alternating variant never strays further from n/2 than the Newman-Conway sequence.</b><br><sub>Open problem settled · formally verified in Lean 4</sub></p>

<p align="center"><sub><a href="paper">paper</a> · <a href="lean">Lean proof</a> · <a href="verify">code</a> · <a href="../">all results</a></sub></p>
<!-- visual:end -->

The Hofstadter–Conway sequence `c(n) = c(c(n-1)) + c(n-c(n-1))` (OEIS A004001) and Alkan's companion `s(n) = n - s(s(n-1)) - s(n-s(n-1))` (OEIS A287422) both start `1, 1`, and on each dyadic block `[2^k, 2^(k+1)]` both `c(n) - n/2` and `s(n) - n/2` trace an arch; the arches of `c` are positive, those of `s` alternate in sign. Alkan conjectured on MathOverflow (question 366772), after checking every `n ≤ 2^32`, that the arches of `s` never rise above those of `c`:

```
|s(n) - n/2| ≤ c(n) - n/2   for every n ≥ 1.
```

The paper proves this. On each block both sequences are encoded by Dyck words, and the words for the next block come from the previous ones by two explicit threshold operators, `F` for `c` and `F` or `G` (alternating with `k`) for `s`. Plain induction fails, because `G` can overtake `F` in one step; the proof instead carries a stronger hypothesis through two steps at once, using a domination lemma for Dyck words that are symmetric under reversal and complement. As by-products, `s` is slow (its increments are 0 or 1), `s(2^k) = 2^(k-1)`, and the sign of `s(n) - n/2` on each block is `(-1)^k`.

Preprint v2, 19 November 2026 (v1: 8 October), not peer reviewed. Zenodo: [doi:10.5281/zenodo.24366939](https://doi.org/10.5281/zenodo.24366939), identical to this folder at tag `hofstadter-conway-comparison-v2`. The lemmas, Proposition 4.1, Corollary 4.2 and Theorem 1 are formally verified in Lean 4 (`lean/`, standard axioms only); Lemma 2.1 is formalised for Dyck words, the case the proof uses, and the counts in the Remark of Section 3 are checked by `verify/` only. That `s` is well defined and slow was stated earlier by Alkan and Aybar (2019 slides, slide 25; Springer 2020) and is reproved here; the comparison theorem and its proof were posted as the author's [MathOverflow answer](https://mathoverflow.net/a/516095) on 16 October 2026, after v1.

**Version 2** (19 November 2026, tag `hofstadter-conway-comparison-v2`): after an independent review by Codex, Alkan and Aybar's earlier statement of the slowness of `s` and the author's MathOverflow answer are cited; the scope of the Lean and computer checks is stated exactly; the description of the perturbation `T` gives the exact heights (lowered by one level and moved one step away from the centre); `verify_paper.py` adds the monotonicity of Lemma 2.3 and compares complete Figure 1 coordinates; the Lean mutants run under the house harness, and the axiom audit is saved in `lean/axiom-validation.txt`. Theorem and proofs unchanged. The author used AI tools (Claude, Anthropic; Codex, OpenAI) in this work, as described in the paper's acknowledgement, and is responsible for its content.

## Contents

- `paper/`: `paper.tex` and `paper.pdf`.
- `lean/`: a Lake project pinned to Lean 4.34.0 and Mathlib v4.34.0. `lean/README.md` maps each result of the paper to its Lean name; `HofstadterConway/Audit.lean` prints the axioms of every one. `SOURCE-SNAPSHOT.json` records the development commit and the hash of every file. `scripts/mutants.toml` plants sixteen wrong changes, each of which must stop `lake build` with a Lean error (run by `scripts/mutate.py`; log in `mutation-validation.log`). `axiom-validation.txt` is the output of `Audit.lean`.
- `verify/verify_paper.py`: written from the paper's definitions alone, it checks Theorem 1 and Corollary 4.2 for every `n ≤ 2^20`, the recurrences (2.2) and (2.3) against the threshold definition on every Dyck word of length at most 12, Proposition 4.1 on every block up to `2^20`, the worked example and the complete coordinates of Figure 1 (read from `paper.tex`), the monotonicity of Lemma 2.3 on every comparable pair of Dyck words of length at most 12, and, on all 26,364 symmetric irreducible Dyck words of length at most 34, the remaining conclusions of Lemmas 2.2(4), 2.3 and 2.4, the midpoint identity, the contact claim and the key lemma (Lemma 2.2(1), (2) and (5) are not tested separately), and the Remark of Section 3; six planted mutants are killed.

## Reproduce

```
cd verify
python3 verify_paper.py                 # standard library only; about a minute
cd ../paper && latexmk -pdf paper.tex
cd ../lean && lake exe cache get && lake build   # builds every module and prints the axiom audit
python3 -I scripts/mutate.py scripts/mutants.toml # sixteen mutants, each rejected with a Lean error
```

## Licence

The paper is released under [CC BY 4.0](../LICENSE-PAPERS), the code under the [MIT licence](../LICENSE-CODE).
