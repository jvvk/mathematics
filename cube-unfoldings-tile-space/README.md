# Every unfolding of the six-dimensional cube tiles five-space

<!-- visual:start -->
<p align="center"><img src="https://raw.githubusercontent.com/jvvk/jvvk/cccf1bc1d96309cd055ad0bad24309c65d1a255a/assets/cube-unfoldings.svg" width="760" alt="Unfolded cubes that tile space"></p>

<p align="center"><b>Every one of the 502,110 unfoldings of the six-dimensional cube tiles five-space with its point reflection, extending Firet's five-cube result.</b><br><sub>Partial progress on an open problem · lemmas in Lean</sub></p>

<p align="center"><sub><a href="paper">paper</a> · <a href="lean">Lean proof</a> · <a href="verify">code</a> · <a href="../">all results</a></sub></p>
<!-- visual:end -->

Cut the boundary of the d-dimensional cube along ridges until it unfolds flat into R^(d-1): the result is a polycube of 2d cells. The ordinary cube has 11 such nets and all of them tile the plane. Joseph O'Rourke asked on MathOverflow ([question 392890](https://mathoverflow.net/q/392890)) whether every unfolding of every cube tiles the space it unfolds into, and if not, up to which dimension. Moritz Firsching settled d = 4 ([a/392828](https://mathoverflow.net/a/392828) to question 199097), and Jelmer Firet settled d = 5 ([a/393006](https://mathoverflow.net/a/393006)): each of the 9,694 unfoldings of the five-cube tiles four-space with translates of P and of its point reflection -P.

This note does d = 6. Each of the 502,110 unfoldings of the six-cube tiles five-space by translates of P and -P, one of each per period (Theorem 1), and every d <= 6 comes with an independently checked certificate. The key step is a reformulation (Lemma 5): such a tiling is the same as a homomorphism φ from Z^(d-1) onto a group G of order 4d, injective on P, with φ(P) + φ(P) ≠ G. Searching homomorphisms instead of tilings takes about an hour for d = 6 on one core. We conjecture that every unfolding of every cube tiles this way; d = 7 has 33,064,966 unfoldings.

Preprint v1, 9 October 2026, not peer reviewed. The d = 5 case is Firet's; new here are d = 6, the rotation-only tilings for d = 4 and the lattice-tiler counts. The quotient lemmas (Lemmas 3 to 5) and Example 6 are formally verified in Lean 4 (`lean/`, standard axioms only); the 502,110 certificates are checked by Python programs that share no code with the search, not in Lean. The author used AI tools (Claude, Anthropic) in this work, as described in the paper's acknowledgement, and is responsible for its content.

## Contents

- `paper/`: `paper.tex`, `paper.pdf`, and `make_figs.py`, which draws the figures from the certificates and checks each drawn tiling for gaps and overlaps.
- `verify/`: the searches (`unfold.c`, `stage2.c`, `gen_nets.py`, `inv.c`), the independent checkers (`verify.py`, `verify2.py`, `geomcheck.py`) and all certificates; `verify/README.md` gives formats and commands.
- `lean/`: a Lake project pinned to Lean 4.34.0 and Mathlib v4.34.0; `lean/README.md` maps results to Lean names, `CheckClaims.lean` prints their axioms, `scripts/mutants.py` runs the mutation tests.

## Reproduce

```
cd verify
python3 verify2.py certificates/cert_d5.txt certificates/inv_d5.txt
gunzip -k certificates/*_d6.txt.gz && python3 verify2.py certificates/nets_d6.txt certificates/inv_d6.txt
cd ../paper && latexmk -pdf paper.tex
cd ../lean && lake exe cache get && lake build LeanProofs && lake env lean CheckClaims.lean
```

`verify/README.md` has the commands that rerun the searches themselves.

## Licence

The paper is released under [CC BY 4.0](../LICENSE-PAPERS), the code under the [MIT licence](../LICENSE-CODE).
