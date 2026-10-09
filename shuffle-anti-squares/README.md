# Shuffle anti-squares of every even length from 24

<!-- visual:start -->
<p align="center"><img src="https://raw.githubusercontent.com/jvvk/jvvk/c7403d6bbbc7106e1780d8c34833854afcb0116f/assets/necklace.svg" width="760" alt="Necklaces no cut can split"></p>

<p align="center"><b>Shuffle anti-squares exist in every even length from 24, as Grytczuk, Pawlik and Pleszczyński conjectured.</b><br><sub>Open problem settled · formally verified in Lean 4</sub></p>

<p align="center"><sub><a href="paper">paper</a> · <a href="lean">Lean proof</a> · <a href="verify">code</a> · <a href="../">all results</a></sub></p>
<!-- visual:end -->

A binary word is a shuffle square if its letters can be coloured with two colours so that each colour, read in order, spells the same word: `1100` is one (both copies spell `10`), `0110` is not. An even word, with an even number of each letter, is a shuffle anti-square if none of its cyclic rotations is a shuffle square. Grytczuk, Pawlik and Pleszczyński found that the shortest anti-squares have length 24 and conjectured that they exist in every even length from 24 upward ([arXiv:2308.13882](https://arxiv.org/abs/2308.13882), Conjecture 1).

The paper proves the conjecture with two explicit families,

- `U_k = 0^(k+9) 1 0^5 11 0^(k+9) 1 0^2 1 0 111` (length 2k + 34), with a short proof by hand, and
- `W_k = 0^(k+5) 1 0^2 1111 0^(k+4) 111 0 1111` (length 2k + 24),

and extends the first: multiplying every zero run of `U_k` by any λ and replacing every one by a block of μ ones, μ odd, still gives an anti-square (Theorem 4; both conditions are needed). Since one cut can only rotate a word, it follows that some even word of every length from 24 needs two cuts before its pieces can be rearranged into a shuffle square (Corollary 6). Grytczuk, Pawlik and Ruciński had found such a word of length 24 and conjectured that two cuts always suffice ([arXiv:2503.22043](https://arxiv.org/abs/2503.22043), Section 6.3); a computer check confirms this for every anti-square up to length 34.

Preprint, 8 October 2026. The author used AI tools (Claude, Anthropic) in this work, as described in the paper's acknowledgements, and takes full responsibility for its content.

## Contents

- `paper/`: `antisquares.tex`, `antisquares.pdf`, the class file `e-jc.sty`, the figure and its generator `make_fig_circle.py`, and the HTML abstract.
- `lean/`: a Lake project pinned to Lean 4.34.0 and Mathlib v4.34.0, with definitions of interleavings, shuffle squares, rotations and cutting written from scratch. `CheckClaims.lean` prints the statement and axioms of every formalised claim: Theorem 2 (`exists_antiSquare`, `W_isAntiSquare`, `U_rotation_not_square`), Theorem 4 with K, λ, μ symbolic (`Blocks.V_isAntiSquare`), `U_k = V(k+9, 1, 1)`, the four splittings showing Theorem 4's conditions are needed, Corollary 6 (`Blocks.two_cuts_needed`) and the two-cut example of `W_0`. Only the standard axioms `propext`, `Classical.choice`, `Quot.sound` are used. These files were built and replayed by the kernel checker (`leanchecker`) in the author's development repository; `SOURCE-SNAPSHOT.json` records that commit and the hash of every file here.
- `verify/`:
  - `search/`: `antisq.c` enumerates necklaces and finds every anti-square (Table 1); `classes.py` counts classes under rotation, reversal and exchange of letters; `ilp_proof.py`, `validate_neg.py`, `mutation.py` are the Z3 proof for `W_k` with its validation and mutants.
  - `cutting/`: `cutdist.c` tests every rotation of every anti-square for a two-cut rearrangement (Section 5); `cutdist_check.py` is a second tester.
  - `recheck/`: programs that share no code with the above. `indep.cpp` recomputes the anti-squares and the two-cut check for every length up to 34; `remark5.py` checks Remark 5 with the buffer method of He and Post.
  - `lean_gen/`: the generators of the Lean proof of Theorem 4. For each of the ten runs in which a cut can fall, `tree.py` uses Z3 only to choose an order of case splits; `emit.py` and `emit_main.py` write them out as Lean, where every case is closed by `omega`. The saved trees (`tree_*.pkl`) regenerate the Lean files byte for byte.
  - `results/`: the anti-square necklaces of lengths 24 to 34.

The counts in Table 1, the absence of anti-squares below length 24, the two-cut check up to length 34 and Remark 5 are exhaustive computer searches, not Lean proofs; each was confirmed by a second, independently written program.

## Reproduce

```
cd verify/search && cc -O2 -o antisq antisq.c && for n in 24 26 28 30 32 34; do ./antisq $n > anti_$n.txt; done
python3 classes.py anti_*.txt                                  # Table 1
python3 ilp_proof.py && python3 validate_neg.py && python3 mutation.py      # needs z3-solver
cd ../cutting && cc -O2 -o cutdist cutdist.c && ./cutdist < ../results/anti_34.txt > /dev/null
cd ../recheck && c++ -O2 -std=c++17 -o indep indep.cpp && ./indep 34 > anti_34.txt && python3 remark5.py
cd ../../paper && latexmk -pdf antisquares.tex
cd ../lean && lake exe cache get && lake build LeanProofs && lake env lean CheckClaims.lean
```

Length 34 takes about 25 minutes for `indep` and a few minutes for the others on one core; the Lean build takes about 15 minutes after the Mathlib cache is fetched.

## Licence

The paper and figure are released under [CC BY 4.0](../LICENSE-PAPERS), the code under the [MIT licence](../LICENSE-CODE).
