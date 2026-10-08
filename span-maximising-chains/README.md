# Which orders maximise the span of a chain?

A planar chain has segments of given distinct lengths, each turning anticlockwise by one of given distinct angles; lengths and angles can be used in any order. Which orders put the end farthest from the start? Arthur Queiroz Moura asked on MathOverflow ([question 442949](https://mathoverflow.net/q/442949)), attributing the problem to Ronaldo Garcia, how many relative orders `a_n` can be optimal when the angles total at most `π/2`.

When the angles total less than `π`, every optimal chain has strictly unimodal lengths with the two shortest at the ends, turns that fall and then rise, and its longest segment at the smallest turn (Theorem 1), confirming observations of Claude Chaunier; this gives an `O(n² log n 2ⁿ)` algorithm (Theorem 2). Exactly three orders occur for four segments (`a₄ = 3`), and an explicit recursive family shows `a_n ≥ b_n` for every `n`, where `b_n = 1, 3, 6, 14, 31, 70, 157, …` is OEIS A006356 (Theorems 3 and 4); in particular `a₇ ≥ 31`, two more than the list in the question. Equality `a_n = b_n` is conjectured and open.

Preprint v1, 8 October 2026, not peer reviewed. Theorem 1 and `a₄ = 3` are formally verified in Lean 4 (`lean/`, standard axioms only). The realisation theorem has a hand proof; it and every numerical claim are checked by exact programs, two of them written independently. The author used AI tools (Codex, OpenAI; Claude, Anthropic) in this work, as described in the paper's acknowledgement, and is responsible for its content.

## Contents

- `paper/`: `paper.tex` and `paper.pdf`.
- `lean/`: a Lake project pinned to Lean 4.34.0 and Mathlib v4.34.0; `lean/README.md` maps results to Lean names, `CheckClaims.lean` prints their axioms, `scripts/mutants.py` runs the mutation tests.
- `verify/`: exact certificates (lengths integer, turns `2 arctan(t/d)`).
  - `verify.py` (with `certificate.py`, `solver.py`, `sweep.py`, `constructive.py`): checks all 124 witnesses for n = 4..8, the Table 1 and Table 2 examples, the exact sweep against unrestricted enumeration (`--audit`), both n = 7 orders against all 1,814,400 classes (`--exhaustive-n7`), and the 290 constructed optima (`--recursive`).
  - `recheck/recheck.py`: an independent recheck sharing no code with the programs above (standard library only); `--fast` skips the two 1.8-million-class enumerations.
  - `explore/`: the linear-programming exclusion test and numerical searches behind Section 7. Exploratory, not proofs.

## Reproduce

```
cd verify
python3 recheck/recheck.py --fast      # about 20 seconds; drop --fast for the full n = 7 enumerations
python3 verify.py                      # default checks; add --audit --exhaustive-n7 --recursive for the rest
cd ../paper && latexmk -pdf paper.tex
cd ../lean && lake exe cache get && lake build LeanProofs && lake env lean CheckClaims.lean
```

## Licence

The paper is released under [CC BY 4.0](../LICENSE-PAPERS), the code under the [MIT licence](../LICENSE-CODE).
