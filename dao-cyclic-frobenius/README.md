# The Frobenius number of Dao's cyclic semigroups

<!-- visual:start -->
<p align="center"><img src="https://raw.githubusercontent.com/jvvk/jvvk/6892ae3679964232632dc72c219c33f02700a0f9/assets/dao-frobenius.svg" width="760" alt="The Frobenius number of Dao's cyclic semigroups"></p>

<p align="center"><b>With x_i = 1 + a_i + a_i a_{i+1} + ⋯ (indices cyclic), the semigroup ⟨x_1, …, x_n⟩ misses exactly up to (n − 1)(a_1⋯a_n − 1), extending ab − 1 for two generators; Hailong Dao's question.</b><br><sub>Open problem settled · formally verified in Lean 4</sub></p>

<p align="center"><sub><a href="paper">paper</a> · <a href="lean">Lean proof</a> · <a href="verify">code</a> · <a href="../">all results</a></sub></p>
<!-- visual:end -->

Fix `n ≥ 2` and positive integers `a_1, …, a_n`, indices read modulo `n`, and put `x_i = 1 + a_i + a_i a_{i+1} + ⋯ + a_i a_{i+1} ⋯ a_{i+n-2}`. Hailong Dao asked on MathOverflow (question 292507, 2018) whether the numerical semigroup `⟨x_1, …, x_n⟩`, with coprime and minimal generators, has Frobenius number `(n − 1)(a_1 a_2 ⋯ a_n − 1)`, extending the classical `ab − 1` for `⟨a + 1, b + 1⟩`. The note proves this for every coprime list. One identity, `a_{i−1} x_i = x_{i−1} + N` with `N = a_1 ⋯ a_n − 1`, turns sums of generators into mixed-radix numerals modulo `N`, and carrying digits shows that each residue class of the semigroup is a ladder: one lowest element, then everything `N` above it.

The formula also follows from a theorem of Goto, Kien, Matsuoka and Truong (J. Algebra 2018) once the semigroup ring is known to be cut out by the 2 × 2 minors of a cyclic 2 × n matrix. That presentation has not been established for this family; the proof here does not use it. Dao also assumed minimal generation. The proof does not need it, but minimality held in every case tested, so the note does not claim this as a strengthening.

Preprint v2, 18 November 2026 (v1: 23 October), not peer reviewed. Zenodo: [doi:10.5281/zenodo.24353723](https://doi.org/10.5281/zenodo.24353723), identical to this folder at tag `dao-cyclic-frobenius-v2`. The case `n = 3` is due to Herzog, Hibi and Stamate ([arXiv:1612.02723](https://arxiv.org/abs/1612.02723v1), Theorem 7.11(ii)); the argument was first posted as the author's [MathOverflow answer](https://mathoverflow.net/a/516265) (22 October 2026). Theorem 1 is formally verified in Lean 4 (`lean/`, standard axioms only); the uniqueness of digit vectors for every value and the per-class ladder equalities are used in the paper but not formalised separately.

**Version 2** (18 November 2026, tag `dao-cyclic-frobenius-v2`): corrections after an independent review by Codex: prior work for `n = 3` credited, the earlier MathOverflow answer cited, the ladder description restricted to nonzero classes with the zero-class formula stated and checked, Lean scope stated exactly, all checks exit nonzero on failure, Lean mutants run under the house harness with diagnostics. Theorem unchanged. The author used AI tools (Claude, Anthropic; ChatGPT, OpenAI) in this work, as described in the paper's acknowledgement, and is responsible for its content.

## Contents

- `paper/`: `paper.tex` and `paper.pdf`.
- `verify/verify_note.py`: Theorem 1 and the ladder description of every nonzero residue class and the zero-class formula (`kN ∈ S` exactly for `k = 0` or `k ≥ n`) against brute force, for all 2,379 coprime lists with `2 ≤ n ≤ 6` and entries at most 8, 8, 5, 4, 3; the worked example; two wrong formulas rejected.
- `verify/recheck.py`: an independent program (no shared code) that recomputes the same Frobenius numbers by shortest paths on residues modulo the smallest generator.
- `verify/remarks.py`: the counts in Remarks 1 and 2 (minimality in 3,703 and 14,459 cases; pseudo-Frobenius sets `{N, …, (n − 1)N}` in 2,186 cases).
- `lean/`: a Lake project pinned to Lean 4.34.0 and Mathlib. `lean/README.md` maps the results to Lean names; `SOURCE-SNAPSHOT.json` records the development commit and file hashes; `scripts/mutants.toml` plants fourteen wrong changes, each rejected.

## Reproduce

```
cd verify
python3 verify_note.py      # a few minutes
python3 recheck.py
python3 remarks.py          # a few minutes
cd ../paper && latexmk -pdf paper.tex
cd ../lean && lake exe cache get && lake build && lake env lean CheckClaims.lean
python3 scripts/mutate.py scripts/mutants.toml    # fourteen mutants, each rejected (rebuilds per mutant)
```

## Licence

The paper is released under [CC BY 4.0](../LICENSE-PAPERS), the code under the [MIT licence](../LICENSE-CODE).
