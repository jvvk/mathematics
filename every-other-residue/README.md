# Every other residue

<!-- visual:start -->
<p align="center"><img src="https://raw.githubusercontent.com/jvvk/jvvk/793b83d1cfc20ceb690263ab666a17b761b223e1/assets/every-other-residue.svg" width="760" alt="Every other residue"></p>

<p align="center"><b>Two sets that each hit every residue mod 2^k once can be matched inside Z/2^(k+1) so that the sums are exactly the even or exactly the odd residues; a case of Snevily's even-order conjecture.</b><br><sub>Answers a question · in Lean</sub></p>

<p align="center"><sub><a href="paper">paper</a> · <a href="lean">Lean proof</a> · <a href="verify">code</a> · <a href="../">all results</a></sub></p>
<!-- visual:end -->

Let `A` and `B` be sets of `2^k` residues modulo `2^(k+1)`, each of which reduces modulo `2^k` to every residue exactly once. A Mathematics Stack Exchange question ([2060312](https://math.stackexchange.com/q/2060312), unanswered since 2016) asks whether `A` and `B` can always be matched so that the `2^k` sums are pairwise distinct modulo `2^(k+1)`. Write `a = r + 2^k e_r` and `b = r + 2^k f_r` with `0 ≤ r < 2^k`, and let `p` be the parity of `∑ e_r + ∑ f_r`, the number of upper-half elements of `A` and `B`.

- **Theorem.** There is a matching whose sums are exactly the residues of parity `p` modulo `2^(k+1)`. No matching has pairwise distinct sums of parity `1 − p`.

The proof splits both sets by their last bit and halves them, giving four instances of the same problem one size down. It matches evens with evens and odds with odds when `p = 0`, and evens with odds when `p = 1`. The impossibility of the other parity follows by adding up all the elements in two ways.

Snevily conjectured in 1999 that two `k`-sets in `ℤ/m` can be matched with distinct sums unless `m` is even and the sets are translates of one cyclic subgroup of even order. The odd-order case is a theorem (Dasgupta, Károlyi, Serra and Szegedy for cyclic groups in 2001, Arsovski in general in 2011); the even-order case is open. Sets as above are never translates of the subgroup of even residues, so the theorem is a case of the even-order conjecture.

Preprint v1, 10 October 2026, not peer reviewed. Both statements of the theorem, and the fact that the sums are never distinct modulo `2^k`, are formally verified in Lean 4 (`lean/`, standard axioms only). The author used AI tools (Claude, Anthropic) in this work, as described in the paper's acknowledgement, and is responsible for its content.

## Contents

- `paper/`: `note.tex` and `note.pdf`. `figs/` holds the TikZ data written by `verify/fig_halving.py`.
- `verify/`:
  - `strong_check.py`: checks the theorem by exhaustive search for `k ≤ 3`, and the impossibility of the other parity for `k ≤ 2`. It also runs the recursive construction on 3000 random instances for each `k ≤ 12`. `MUTANT=1` (the two cases swapped) and `MUTANT=2` (a parity count that ignores `B`) must print `FAIL`.
  - `pairing.c`: an independent exhaustive search over all pairs for `k ≤ 3`. With mutant `1` it demands distinct sums only modulo `2^k`, which must fail.
  - `fig_halving.py`: Figure 1, one halving step on the example of Table 1.
- `lean/`: a Lake project pinned to Lean 4.34.0 and Mathlib v4.34.0. `lean/README.md` maps results to Lean names, `CheckClaims.lean` prints their axioms, and `scripts/mutants.py` runs the mutation tests.

## Reproduce

```
cd verify && python3 strong_check.py && MUTANT=1 python3 strong_check.py | tail -1 && MUTANT=2 python3 strong_check.py | tail -1
cc -O2 -o pairing pairing.c && ./pairing 3 && ./pairing 3 0 1
python3 fig_halving.py
cd ../paper && latexmk -pdf note.tex
cd ../lean && lake exe cache get && lake build LeanProofs && lake env lean CheckClaims.lean
```

## Licence

The paper is released under [CC BY 4.0](../LICENSE-PAPERS), the code under the [MIT licence](../LICENSE-CODE).
