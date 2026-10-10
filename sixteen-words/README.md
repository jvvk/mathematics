# Sixteen words cover all 15-bit strings

<!-- visual:start -->
<p align="center"><img src="https://raw.githubusercontent.com/jvvk/jvvk/97c3ad8bc715004adbf4efa8b734cd4453ae1ef3/assets/sixteen-words.svg" width="760" alt="Sixteen words cover all 15-bit strings"></p>

<p align="center"><b>Deleting five bits from every 15-bit string can leave just 16 different strings, down from 17 in 2013, so the growth rate of the n/3-deletion problem is at most 16^(1/15) &lt; 1.2031; among symmetric sets 16 is optimal.</b><br><sub>Partial progress · rate argument formally verified in Lean · cover and optimality by certified computation</sub></p>

<p align="center"><sub><a href="paper">paper</a> · <a href="lean">Lean proof</a> · <a href="verify">code</a> · <a href="../">all results</a></sub></p>
<!-- visual:end -->

From every binary string of length `n = 3k` delete `k` bits, choosing the deletions so that as few distinct strings of length `2k` remain as possible ([MathOverflow 142857](https://mathoverflow.net/q/142857), 2013). The least number `H(3k, k)` grows like `α^(3k)`; the 2013 discussion showed `α` exists (blocks and Fekete's lemma), bounded it below by `2^(5/3)/3 ≈ 1.058`, and above by small covers, the best being a 17-word cover for `n = 15`: `α ≤ 17^(1/15) ≈ 1.2079`.

**Theorem.** These sixteen strings of length 10 cover length 15 (every 15-bit string contains one as a subsequence), and none can be dropped:

```
0000000000 0000000011 0000111110 0011001100 0011111111 0110000110 0110101001 0111110000
1000001111 1001010110 1001111001 1100000000 1100110011 1111000001 1111111100 1111111111
```

So `H(15,5) ≤ 16` and `α ≤ 16^(1/15) < 1.2031`. The set is closed under complement and reversal, and **no such symmetric set of 15 or fewer strings covers length 15**: found by CP-SAT, confirmed by Glucose on an independent encoding, whose DRAT proof of unsatisfiability is checked by drat-trim. Whether an asymmetric 15-word cover exists is open.

Preprint v1, 10 October 2026, not peer reviewed and not yet independently reviewed. The block argument, the submultiplicativity of `H`, Fekete's limit and the bound on `α` from a 16-word cover are formally verified in Lean 4 (`lean/`, standard axioms only); the cover itself and the symmetric optimum are finite computations checked by independent programs and a proof checker. The author used AI tools (Claude, Anthropic) in this work, as described in the paper's acknowledgement, and is responsible for its content.

## Contents

- `paper/`: `note.tex`, `note.pdf`, the figure `fig_cover.tex` and its generator `make_fig.py`.
- `lean/`: a Lake project pinned to Lean 4.34.0 and Mathlib v4.34.0; `lean/README.md` maps results to Lean names, `CheckClaims.lean` prints their axioms, `scripts/mutants.py` runs 9 mutation tests.
- `verify/`:
  - `verify15.py`: checks the cover over all `2^15` strings, and that each of the 16 single-word deletions fails (pure Python).
  - `cover.py`, `cover_sym.py`: the CP-SAT searches (OR-Tools); `sym15.log` (symmetric optimum 16), `asym15.log` (unrestricted, 100 s, unknown), `run18.log` (an inconclusive `n = 18` symmetric run).
  - `check.py`: the rates and orbit structure stated in the note, with four mutants.
  - `recheck/recheck_sym.py`: an independent check (own subsequence test, own CNF and cardinality encoding, Glucose via PySAT): replays the published cover, finds a symmetric 16-cover, refutes size 15 and writes a DRAT proof; two mutants. `sym15.drat.gz` is that proof.

## Reproduce

```
cd verify
python3 verify15.py && python3 check.py
python3 cover.py 15 5 --sym                     # needs ortools; a few seconds
cd recheck && python3 recheck_sym.py --proof sym15.drat     # needs python-sat; about two minutes
# then, with drat-trim (github.com/marijnheule/drat-trim):  drat-trim sym15.cnf sym15.drat
cd ../../paper && latexmk -pdf note.tex
cd ../lean && lake exe cache get && lake build LeanProofs && lake env lean CheckClaims.lean
```

## Licence

The paper is released under [CC BY 4.0](../LICENSE-PAPERS), the code under the [MIT licence](../LICENSE-CODE).
