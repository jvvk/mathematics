# A comparison theorem for the Hofstadter–Conway $10,000 sequence and its alternating variant

The Hofstadter–Conway sequence `c(n) = c(c(n-1)) + c(n-c(n-1))` (OEIS A004001) and Alkan's companion `s(n) = n - s(s(n-1)) - s(n-s(n-1))` (OEIS A287422) both start `1, 1`, and on each dyadic block `[2^k, 2^(k+1)]` both `c(n) - n/2` and `s(n) - n/2` trace an arch; the arches of `c` are positive, those of `s` alternate in sign. Alkan conjectured on MathOverflow (question 366772), after checking every `n ≤ 2^32`, that the arches of `s` never rise above those of `c`:

```
|s(n) - n/2| ≤ c(n) - n/2   for every n ≥ 1.
```

The paper proves this. On each block both sequences are encoded by Dyck words, and the words for the next block come from the previous ones by two explicit threshold operators, `F` for `c` and `F` or `G` (alternating with `k`) for `s`. Plain induction fails, because `G` can overtake `F` in one step; the proof instead carries a stronger hypothesis through two steps at once, using a domination lemma for Dyck words that are symmetric under reversal and complement. As by-products, `s` is slow (its increments are 0 or 1), `s(2^k) = 2^(k-1)`, and the sign of `s(n) - n/2` on each block is `(-1)^k`.

Preprint v1, 8 October 2026, not peer reviewed. Every result of the paper is formally verified in Lean 4 (`lean/`, standard axioms only). The exposition has not yet been independently reviewed. The author used AI tools (Claude, Anthropic; Codex, OpenAI) in this work, as described in the paper's acknowledgement, and is responsible for its content.

## Contents

- `paper/`: `paper.tex` and `paper.pdf`.
- `lean/`: a Lake project pinned to Lean 4.34.0 and Mathlib v4.34.0. `lean/README.md` maps each result of the paper to its Lean name; `HofstadterConway/Audit.lean` prints the axioms of every one. `SOURCE-SNAPSHOT.json` records the development commit and the hash of every file. `mutants.sh` plants sixteen wrong changes and checks that each fails to build.
- `verify/verify_paper.py`: written from the paper's definitions alone, it checks Theorem 1 and Corollary 4.2 for every `n ≤ 2^20`, the recurrences (2.2) and (2.3) against the threshold definition on every Dyck word of length at most 12, Proposition 4.1 on every block up to `2^20`, the worked example and the coordinates of Figure 1 (read from `paper.tex`), Lemmas 2.2 to 2.4 and the key lemma on all 26,364 symmetric irreducible Dyck words of length at most 34, and Remark 3.2; five planted mutants are killed.

## Reproduce

```
cd verify
python3 verify_paper.py                 # standard library only; about a minute
cd ../paper && latexmk -pdf paper.tex
cd ../lean && lake exe cache get && lake build   # builds every module and prints the axiom audit
./mutants.sh                                     # sixteen mutants, each rejected
```

## Licence

The paper is released under [CC BY 4.0](../LICENSE-PAPERS), the code under the [MIT licence](../LICENSE-CODE).
