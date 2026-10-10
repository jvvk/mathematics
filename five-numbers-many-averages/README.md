# Five numbers, many averages

<!-- visual:start -->
<p align="center"><img src="https://raw.githubusercontent.com/jvvk/jvvk/b93403b61d53a1c64a2e4cf938cfa82dbf948e47/assets/five-numbers.svg" width="760" alt="Five numbers, many averages"></p>

<p align="center"><b>Replacing two numbers by their average, the five integers (5N, 0, 4N, 3N±5, 3N±5) with N = 2ᵏ⁺¹ need exactly k + 3 moves to become equal, so five numbers have no bound on the shortest solution.</b><br><sub>Partial progress · formally verified in Lean · which lists are solvable is open</sub></p>

<p align="center"><sub><a href="paper">paper</a> · <a href="lean">Lean proof</a> · <a href="verify">code</a> · <a href="../">all results</a></sub></p>
<!-- visual:end -->

A move replaces two numbers by two copies of their average. jh w asked on MathOverflow ([question 421671](https://mathoverflow.net/q/421671)) which lists of rationals can be made all equal in finitely many moves. Powers of two always can; for any other count the generic list cannot (Shi, Li, Johansson and Johansson, 2016); three numbers can exactly when they are in arithmetic progression, and five can when one of them already equals the mean (Brendan McKay, in the comments). The full question is open.

**Theorem.** Let `k ≥ 1`, `N = 2^(k+1)`, `ε = (−1)^k`. The five integers `(5N, 0, 4N, 3N + 5ε, 3N + 5ε)` can be made equal, and the least number of moves is exactly `k + 3`. For `k ≥ 2` no proper subset has the same mean as the whole.

For example `(40, 0, 32, 29, 29)` (`k = 2`, mean 26) takes five moves and not four. So for five numbers there is no bound on the length of the shortest solution that depends only on the count: a decision procedure, if one exists, must look at the size of the numbers.

The upper bound uses a triple `(s, s, −2s)` that a move turns into `(−s/2, −s/2, s)`, creeping towards its mean. For the lower bound, after `r` moves every entry is a combination of the inputs with weights `m_i / 2^r`; a divisibility argument shows no entry can equal the mean before move `k`. After that, the number of entries at the mean grows only in steps of 2 and can never be 4, so three more moves are needed.

Preprint v1, 10 October 2026, not peer reviewed and not yet independently reviewed. Every step of the proof is formally verified in Lean 4 (`lean/`, standard axioms only). The author used AI tools (Claude, Anthropic) in this work, as described in the paper's acknowledgement, and is responsible for its content.

## Contents

- `paper/`: `note.tex`, `note.pdf` and the figure sources `fig_*.tex`.
- `lean/`: a Lake project pinned to Lean 4.34.0 and Mathlib v4.34.0; `lean/README.md` maps results to Lean names, `CheckClaims.lean` prints their axioms, `scripts/mutants.py` runs 9 mutation tests.
- `verify/`:
  - `check.py` asserts every number in the note in exact arithmetic: the rows and count column of Figure 1, the triple of Figure 2, the strategy for `k ≤ 60`, the least number of moves for `k ≤ 6` by complete search, the integer form, and the subsets for `k ≤ 40`; four mutants are rejected.
  - `recheck/recheck.py`: an independent check sharing no code with `check.py` (integer arithmetic, labelled iterative deepening for `k ≤ 5` with replayed witnesses, subsets by bitmask) and three mutants of its own. `recheck-full.log` is the full run.

## Reproduce

```
cd verify
python3 check.py              # a few seconds
python3 recheck/recheck.py    # under a second
cd ../paper && latexmk -pdf note.tex
cd ../lean && lake exe cache get && lake build LeanProofs && lake env lean CheckClaims.lean
```

## Licence

The paper is released under [CC BY 4.0](../LICENSE-PAPERS), the code under the [MIT licence](../LICENSE-CODE).
