# Infinitely many integers that are not quotients of zero-free balanced ternary numbers

<!-- visual:start -->
<p align="center"><img src="https://raw.githubusercontent.com/jvvk/jvvk/c7403d6bbbc7106e1780d8c34833854afcb0116f/assets/balanced-ternary.svg" width="760" alt="Quotients of balanced ternary numbers"></p>

<p align="center"><b>Guy's question F31: infinitely many integers are not a ratio of two numbers whose balanced-ternary digits are all 1 or −1.</b><br><sub>Open problem settled · formally verified in Lean 4</sub></p>

<p align="center"><sub><a href="paper">paper</a> · <a href="lean">Lean proof</a> · <a href="verify">code</a> · <a href="../">all results</a></sub></p>
<!-- visual:end -->

Let `B` be the positive integers whose balanced ternary digits are all `1` or `-1`. Selfridge and Lacampagne asked whether every integer not divisible by 3 is a quotient of two elements of `B` (Guy, *Unsolved Problems in Number Theory*, F31). Coppersmith found the exception 247, and Bai, Meleshko, Riasat and Shallit (*Integers* 22, 2022) found seventeen below 3650 and wrote that there are likely infinitely many, "but we have no proof".

This paper proves it. `4·3^k + 5`, `4·3^k − 5`, `8·3^k + 7` and `8·3^k + 17` lie outside `B/B` for every `k ≥ 5`, and `8·3^k − 7` for every `k ≥ 7`, each bound sharp (Theorem 1.1); eight further families are exceptions along residue classes of `k` (Theorem 1.3). The proof finds, for each family, a set of carries of size linear in `k` that is closed under the carry map of multiplication by `n` and contains no accepting carry; for `4·3^k + 5` it is short enough to check by hand (Section 3). Of the 200 exceptions below `10^8`, 75 are covered. One new data point for the companion problem with digits 0 and 1: `621·3^16 − 20` is an exception.

Preprint v3, 24 October 2026 (v1: 8 October 2026), not peer reviewed. The thirteen non-membership statements of Theorems 1.1 and 1.3 are formally verified in Lean 4 (`lean/`, standard axioms only); their sharpness and Proposition 6.1 are checked by `verify/check_paper.py`, which also recomputes the other finite claims, and the list of exceptions below `10^8` comes from `verify/search.c`; the exposition has not yet been independently reviewed. The author used an AI tool (Claude, Anthropic) in this work, as described in the paper's declaration of generative AI use, and is responsible for its content.

**Version 2** (23 October 2026, tag `balanced-ternary-quotients-v2`): expository revision of the paper (conditions (i) and (iii) of Proposition 2.2 now argued in the text instead of called immediate). The results, programs and Lean files are unchanged from v1.

**Version 3** (24 October 2026, tag `balanced-ternary-quotients-v3`): credits Shallit (OEIS A351243) for the `3^k + 4` question, narrows the statements of what Lean and the programs verify, states the normalisation behind Table 2 (and checks the 77 unnormalised pairs), and corrects a sign in the upper-gap test of `symproof.py`; its five certificates were rerun and pass. The theorems and the Lean files are unchanged.

## Contents

- `paper/`: `quotients.tex`, `quotients.pdf`, the appendix tables `tables.tex` and Figure 1.
- `lean/`: a Lake project pinned to Lean 4.34.0, core library only, about 31,000 lines. `lean/README.md` maps each result to its Lean name; `BalancedTernary/Audit.lean` prints the axioms of every one; `generator/` rewrites the thirteen family proofs byte for byte from the carry sets; `mutants.py` plants eight wrong changes and checks that each fails. `SOURCE-SNAPSHOT.json` records the development commit and the hash of every file.
- `verify/`:
  - `check_paper.py`: the numbers and finite claims of the paper from the definitions (the seventeen exceptions, Table 1, the digit expansions, the witnesses including the smallest one for `8·3^6 − 7`, each Appendix A set against conditions (i) to (iv) for `14 ≤ k ≤ 40` and against the reachable set, each listed exception outside `B/B`, the counts 50, 75, 136, 21 and 77, Table 2, the `621·3^(4k) − 20` carry counts), with six planted mutants. It does not re-prove that the list below `10^8` is complete (that is `search.c`), nor read `paper/tables.tex` or the carry-count column of `exceptions_1e8.txt`. Standard library only, seconds.
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
