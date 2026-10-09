# Even and odd Dyck paths

<!-- visual:start -->
<p align="center"><img src="https://raw.githubusercontent.com/jvvk/jvvk/3669007c9373f8a2d3e973c5658b5b6b3cc7fcc5/assets/dyck-signs.svg" width="760" alt="Even and odd Dyck paths"></p>

<p align="center"><b>Weight a Dyck path by its valley positions: even minus odd is the number of symmetric paths. Cigler's question, a combinatorial proof.</b><br><sub>Open problem settled · formally verified in Lean · one classical identity quoted</sub></p>

<p align="center"><sub><a href="paper">paper</a> · <a href="lean">Lean proof</a> · <a href="verify">code</a> · <a href="../">all results</a></sub></p>
<!-- visual:end -->

Weight a Dyck path by the sum of the positions of its valleys, its major index. Johann Cigler observed that among the paths of semilength `n` with `k` valleys, those of even weight outnumber those of odd weight by exactly the number of symmetric paths with `k` valleys. By an identity of Fürlinger and Hofbauer this says that the `q`-Narayana number `N_{n,k}(q)` at `q = -1` counts symmetric Dyck paths. Cigler proved it algebraically and asked on MathOverflow ([question 501839](https://mathoverflow.net/q/501839)) for a direct combinatorial proof.

The note gives one (Theorem 1). Valley coordinates turn each path into a two-coloured Motzkin word in which the sign is a product of local signs (Lemmas 1 and 2). Swapping letters inside the first pair that has a partner is a sign-reversing involution whose fixed words all have sign `+1` (Lemma 3). Halving the fixed words and reading off the last departures from each level matches them with the symmetric paths (Lemma 4). The survivors are not the symmetric paths themselves, and cannot be: for odd `n` and `k` every symmetric path has odd weight. For even `n` the value at `q = -1` is also the half-turn case of a cyclic sieving theorem of Reiner, Stanton and White for noncrossing partitions, proved there by computing both sides.

Preprint v1, 10 October 2026, not peer reviewed and not yet independently reviewed. The whole argument, from Dyck paths written as lists of steps to Theorem 1, is formally verified in Lean 4 (`lean/`, standard axioms only); the identity of Fürlinger and Hofbauer is quoted, and checked by computer for `n ≤ 8`. The author used AI tools (Claude, Anthropic) in this work, as described in the paper's acknowledgement, and is responsible for its content.

## Contents

- `paper/`: `note.tex`, `note.pdf`, the figure sources `fig_*.tex` and `gen_figs.py`, which writes them from the checked words.
- `lean/`: a Lake project pinned to Lean 4.34.0 and Mathlib v4.34.0; `lean/README.md` maps results to Lean names, `CheckClaims.lean` prints their axioms and evaluates the definitions on small cases, `scripts/mutants.py` runs 12 mutation tests.
- `verify/`:
  - `involution.py`: checks every claim of Sections 3 to 5 (encoding, involution, signs, fixed points, bijection) for all paths with `n ≤ 12`; `mutants.py` checks that four wrong variants fail.
  - `recheck/recheck.py`: an independent check from the definitions, sharing no code with `involution.py`: Theorem 1 and the `q`-Narayana value at `-1` (exact polynomial arithmetic) for `n ≤ 10`, the identity of Fürlinger and Hofbauer for `n ≤ 8`, every example in the text, Lemmas 1 to 4, and three mutants. `recheck-full.log` is the full run.

## Reproduce

```
cd verify
python3 involution.py 12 && python3 mutants.py
python3 recheck/recheck.py 10
cd ../paper && latexmk -pdf note.tex
cd ../lean && lake exe cache get && lake build LeanProofs && lake env lean CheckClaims.lean
```

The Python programs need only the standard library.

## Licence

The paper is released under [CC BY 4.0](../LICENSE-PAPERS), the code under the [MIT licence](../LICENSE-CODE).
