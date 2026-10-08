# Infinitely many integers that are not quotients of zero-free balanced ternary numbers

Let `B` be the positive integers whose balanced ternary digits are all `1` or `-1`. Selfridge and Lacampagne asked whether every integer not divisible by 3 is a quotient of two elements of `B` (Guy, *Unsolved Problems in Number Theory*, F31). Coppersmith found the exception 247, and Bai, Meleshko, Riasat and Shallit (*Integers* 22, 2022) found seventeen below 3650 and wrote that there are likely infinitely many, "but we have no proof".

This paper proves it. `4·3^k + 5`, `4·3^k − 5`, `8·3^k + 7` and `8·3^k + 17` lie outside `B/B` for every `k ≥ 5`, and `8·3^k − 7` for every `k ≥ 7`, each bound sharp (Theorem 1.1); eight further families are exceptions along residue classes of `k` (Theorem 1.3). The proof finds, for each family, a set of carries of size linear in `k` that is closed under the carry map of multiplication by `n` and contains no accepting carry; for `4·3^k + 5` it is short enough to check by hand (Section 3). Of the 200 exceptions below `10^8`, 75 are covered. One new data point for the companion problem with digits 0 and 1: `621·3^16 − 20` is an exception.

Preprint v1, 8 October 2026, not peer reviewed. Theorems 1.1 and 1.3 are formally verified in Lean 4 (`lean/`, standard axioms only), and every number quoted in the paper is recomputed by `verify/check_paper.py`; the exposition has not yet been independently reviewed. The author used an AI tool (Claude, Anthropic) in this work, as described in the paper's declaration of generative AI use, and is responsible for its content.

## Contents

- `paper/`: `quotients.tex`, `quotients.pdf`, the appendix tables `tables.tex` and Figure 1.
- `lean/`: a Lake project pinned to Lean 4.34.0, core library only, about 31,000 lines. `lean/README.md` maps each result to its Lean name; `BalancedTernary/Audit.lean` prints the axioms of every one; `generator/` rewrites the thirteen family proofs byte for byte from the carry sets; `mutants.py` plants eight wrong changes and checks that each fails. `SOURCE-SNAPSHOT.json` records the development commit and the hash of every file.
- `verify/`:
  - `check_paper.py`: every number and finite claim of the paper from the definitions (the seventeen exceptions, Table 1, the digit expansions, the witnesses including the smallest one for `8·3^6 − 7`, each Appendix A set against conditions (i) to (iv) for `14 ≤ k ≤ 40` and against the reachable set, the counts 50, 75, 136 and 21, Table 2, the `621·3^(4k) − 20` carry counts), with six planted mutants. Standard library only, seconds.
  - `carry_sets.json` (Appendix A) and `exceptions_1e8.txt` (the 200 exceptions below `10^8` with their reachable carry counts).
  - `search.c`: the exhaustive search that produced `exceptions_1e8.txt`.
  - `symproof.py` (with `prover.py`, `reach.py`): the independent symbolic checker in Python for the five families of Theorem 1.1.
  - `make_fig_carries.py`: Figure 1.

## Reproduce

```
cd verify
python3 check_paper.py                          # every number in the paper, seconds (about 1 GB for the last check)
python3 symproof.py 4 5 cert                    # independent all-k proof of one family of Theorem 1.1
cc -O2 -o search search.c && ./search 1 100000000 > ex.txt   # the 200 exceptions, about 25 minutes
cd ../paper && latexmk -pdf quotients.tex
cd ../lean && lake build && python3 mutants.py
```

## Licence

The paper and figure are released under [CC BY 4.0](../LICENSE-PAPERS), the code under the [MIT licence](../LICENSE-CODE).
