# Fences do not maximise orbits of linear extensions

<!-- visual:start -->
<p align="center"><img src="https://raw.githubusercontent.com/jvvk/jvvk/95d4ca70d3efe0a0745cf69ffcfe3f69c0489901/assets/fences-orbits.svg" width="760" alt="Fences do not maximise orbits of linear extensions"></p>

<p align="center"><b>The posets with the most orbits of linear extensions are found exactly for n ≤ 11, and for every n ≥ 58 none is a disjoint union of fences; Richard Stanley's question.</b><br><sub>Open problem partly settled · Theorem 2 for n ≥ 181 formally verified in Lean 4</sub></p>

<p align="center"><sub><a href="paper">paper</a> · <a href="lean">Lean proof</a> · <a href="verify">code</a> · <a href="../">all results</a></sub></p>
<!-- visual:end -->

The automorphism group of a finite poset `P` acts freely on its linear extensions, so the number of orbits is `f(P) = e(P)/#Aut(P)`. Richard Stanley asked on MathOverflow (question 516140) about the largest value `g(n)` over `n`-element posets, and whether the maximisers are disjoint unions of fences. The note finds `g(n)` and every maximiser for `n ≤ 11` by exhaustive search: fence unions maximise exactly for `n ≤ 7` and `n = 9`, and the first failure is an eight-element poset with `f = 2384` against `2100` for the best fence union. It then proves that for every `n ≥ 58` no maximiser is a union of fences. The proof sets Graham's construction (posted as an answer on the thread, credited in the paper) against a new bound for fence unions: `t` disjoint comparable pairs allow at most `n!/2^t` linear extensions. The range `12 ≤ n ≤ 57` stays open.

Preprint v1, 23 October 2026, not peer reviewed. Theorem 2 for `n ≥ 181`, with Lemma 1, Proposition 2 and Lemma 3, is formally verified in Lean 4 (`lean/`, standard axioms only); the range `58 ≤ n ≤ 180` and Theorem 1 are exact computations. The author used AI tools (Claude, Anthropic) in this work, as described in the paper's acknowledgement, and is responsible for its content.

## Contents

- `paper/`: `paper.tex` and `paper.pdf`.
- `verify/search.sh`: Theorem 1. Every poset on `n ≤ 11` points from nauty's `genposetg`, `e(P)` by dynamic programming over down-sets and `#Aut(P)` by backtracking (`orbits.c`), maxima by `maxima.py`; the output is compared with `expected.txt` (poset counts match OEIS A000112).
- `verify/sage_g8.sage`: an independent recomputation of `g(n)` and the maximisers for `n ≤ 8` with Sage's own poset generator and counters. `describe.py` decodes a maximiser into its components.
- `verify/fences.py`: the exact best fence union for every `n ≤ 200` against Graham's bound `(n − J(n))!`, the brute-force checks of `e(Z_m) = E_m` and `#Aut(Z_m)`, and the exact check of inequality (2).
- `verify/recheck_fences.py`: an independent program (no shared code) for the same fence-union comparison.
- `lean/`: a Lake project pinned to Lean 4.34.0 and Mathlib. `lean/README.md` maps the results to Lean names; `SOURCE-SNAPSHOT.json` records the development commit and file hashes; `scripts/mutants.toml` plants 61 wrong changes, each rejected.

## Reproduce

```
cd verify
python3 fences.py                 # ALL PASS
python3 recheck_fences.py         # ALL PASS
./search.sh 11                    # needs nauty's genposetg on PATH and a C compiler; n = 11 takes a few minutes
sage sage_g8.sage                 # optional, needs SageMath
cd ../paper && latexmk -pdf paper.tex
cd ../lean && lake exe cache get && lake build && lake env lean CheckClaims.lean
python3 scripts/mutate.py scripts/mutants.toml    # 61 mutants, each rejected (rebuilds per mutant)
```

## Licence

The paper is released under [CC BY 4.0](../LICENSE-PAPERS), the code under the [MIT licence](../LICENSE-CODE).
