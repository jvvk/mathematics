# Precarious necklaces

<!-- visual:start -->
<p align="center"><img src="https://raw.githubusercontent.com/jvvk/jvvk/73a2f3b94e402965c8389a1c994c30bce081c60f/assets/precarious.svg" width="760" alt="Precarious necklaces"></p>

<p align="center"><b>The shortest necklace with no rotational symmetry that gains one whenever a colour is removed has 2m·P_m beads for 2m colours and P_m(2m·p_{m+1} + 1) for 2m + 1, where P_m is the product of the first m primes.</b><br><sub>Question answered · every step in Lean</sub></p>

<p align="center"><sub><a href="paper">paper</a> · <a href="lean">Lean proof</a> · <a href="verify">code</a> · <a href="../">all results</a></sub></p>
<!-- visual:end -->

A necklace of coloured beads is *precarious* if no rotation short of a full turn fixes it, but removing all the beads of any one colour leaves a necklace that some rotation does fix. Philip Weiss asked on MathOverflow ([question 515996](https://mathoverflow.net/q/515996)) for the length `a(k)` of the shortest precarious necklace with `k` colours, and gave `a(2), …, a(5) = 4, 14, 24, 126`.

This note proves:

- **Theorem 1.** `a(2m) = 2m·P_m` and `a(2m+1) = P_m·(2m·p_{m+1} + 1)`, where `p_i` is the `i`-th prime and `P_m = p_1 ⋯ p_m`. The sequence continues `180, 1290, 1680, 18690, 23100, …`.
- **Theorem 2.** Keeping any `s` of the `k` colours (`1 ≤ s < k`) instead of removing one, the shortest such necklace has length `s·P_{⌊s/2⌋+1} + (k − s)·P_{⌈s/2⌉}`. Theorem 1 is the case `s = k − 1`; `s = 1, 2, 3` give `2k`, `2k + 8` and `6k`.
- **Lemma 3**, the key step: a word is a `q`-th power as soon as every two-letter projection of it is.

The constructions also satisfy more than is asked: removing any nonempty set of colours, not just one, leaves a symmetric necklace.

Preprint v1, 20 October 2026, not peer reviewed. Every result is formally verified in Lean 4 (`lean/`, standard axioms only). The author used AI tools (Claude, Anthropic, and a second AI system for an independent check) in this work, as described in the paper's acknowledgements, and is responsible for its content.

## Contents

- `paper/`: `precarious-necklaces.tex` and `precarious-necklaces.pdf`.
- `verify/`:
  - `recheck_paper.py`: an independent check of every finite claim in the paper, sharing no code with the other scripts. It tests Lemmas 1 and 3 exhaustively on short words, both figures, the values of Theorem 1 to `k = 10`, Table 1 (parsed from the `.tex`), the constructions of Section 3 for all `1 ≤ s < k ≤ 7`, the remark for `k ≤ 6`, and the exhaustive minima for `(k, s) = (2, 1), (3, 1), (4, 1), (3, 2)`. Runs in a few seconds. `MUTANT=1` corrupts the even construction; it must end in `FAIL`.
  - `neck.py`, `odd.py`, `ext.py`, `framework.py`, `closed.py`: the working programs: the pair-rhythm constructions for `k ≤ 8`, the exhaustive search for `a(3) = 14` and the three-colour words of length 14 to 16, the `s = 2` construction, and the comparison of formula (2) with an exhaustive optimisation over prime assignments. Each runs in under 20 seconds.
- `lean/`: a Lake project pinned to Lean 4.34.0 and Mathlib v4.34.0; `lean/README.md` maps results to Lean names, `CheckClaims.lean` prints their axioms, `scripts/mutants.py` runs the 39 mutation tests.

## Reproduce

```
cd verify && python3 recheck_paper.py && MUTANT=1 python3 recheck_paper.py | tail -1
python3 neck.py && python3 odd.py && python3 ext.py && python3 closed.py
cd ../paper && latexmk -pdf precarious-necklaces.tex
cd ../lean && lake exe cache get && lake build LeanProofs && lake env lean CheckClaims.lean
```

## Licence

The paper is released under [CC BY 4.0](../LICENSE-PAPERS), the code under the [MIT licence](../LICENSE-CODE).
