# Bogner's strange operator carries a √2 twist

<!-- visual:start -->
<p align="center"><img src="https://raw.githubusercontent.com/jvvk/jvvk/4c7e74a608fb9968b9a93d987058b761e680a6e7/assets/strange-operator-twist.svg" width="760" alt="Bogner's strange operator carries a √2 twist"></p>

<p align="center"><b>A Calabi-Yau operator with integral period, a mirror map integral in every degree computed, and fractional instanton numbers: read through a multicover formula twisted by √2, they become integers, as the cusp predicts; proved at each p ≥ 5 given a Frobenius structure.</b><br><sub>Explains a puzzle · conditional theorem · elementary algebra in Lean</sub></p>

<p align="center"><sub><a href="paper">paper</a> · <a href="lean">Lean proof</a> · <a href="verify">code</a> · <a href="../">all results</a></sub></p>
<!-- visual:end -->

Bogner found a fourth order differential operator of Calabi-Yau type,

`P = θ⁴ − 8x(2θ+1)²(5θ²+5θ+2) + 192x²(2θ+1)(3θ+2)(3θ+4)(2θ+3)`,

whose holomorphic period has integer coefficients, and whose mirror map and Yukawa coupling have integer coefficients in every degree computed (through 110; no proof is known), while its instanton numbers do not: `n₃ = −1880/9`, `n₅ = −3541608/25`, and `n_p` has denominator `p²` at every prime tested. Van Straten called this "rather puzzling" (arXiv:1704.00164, pp. 28-29), and Almkvist and van Straten recorded it again in their 2023 paper on degree two operators.

**Results.**

- **Structure (due to Bogner and Reiter).** `P` is the Hadamard product of `Σ binom(2n,n) xⁿ` with the symmetric square of a second order operator `D`: this is entry 8′ of the table in Bogner and Reiter (arXiv:1211.3945, 2012; Exp. Math. 26, 2017), who also noted that the instanton numbers are not integral. We record that `D` is modular: `x` is a Hauptmodul for an index four subgroup of `PSL₂(ℤ)` with `j = (16x−1)³/(4x⁴)`.
- **The twist.** Read through a multicover formula twisted by `√2` (weights `(2/k)^d 2^(d(k−1)/2)`), the instanton numbers are integers for every `d ≤ 110`. The twist is predicted by the cusp, where `x⁴ ≈ −q_τ/4`.
- **Conditional theorem.** A twisted form of a theorem of Beukers and Vlasenko proves the twisted integrality at each prime `p ≥ 5`, given a `p`-adic Frobenius structure with a specified first constant (Hypothesis F). The truncations of that structure exist at `p = 5, 7, 11, 13, 17` in every degree tested, up to degree 1000 at `p = 5`, and each forces the predicted constant.
- **What does not work.** Rescaling the coordinate (algebraic irrational scalings, conditional on an all-prime congruence; rational scalings of height at most 3000); the strong structure at `p = 3`; Laurent models that split along the Hadamard product; a general transfer of Frobenius structures through the Hadamard product, for structures integral through degree 60.

Hypothesis F is open, so the integrality of the twisted numbers is proved only conditionally. The general idea of number-field-valued 3-functions for operators of this kind was mentioned by Schwarz, Vologodsky and Walcher (arXiv:1702.07135, footnote 9); the decomposition is Bogner and Reiter's; the modular description of `D`, the twist, the conditional theorem and the certificates are new as far as we know.

Preprint v2, 25 October 2026 (v1: 11 October 2026), not peer reviewed. The elementary algebra is formally verified in Lean 4 (`lean/`, standard axioms only): the recurrence of `P = I ⋆ L`, the twist constant `c_p ≡ 1 (mod p)` and `c_p⁴ = 4^(p−1)`, the weight identity `w_d(pk) = c_p^(dk) w_d(k)`, `p ∣ binom(2p−2, p−1)`, and the arithmetic at the prime 3. The `p`-adic Frobenius theory and the conditional theorem are not formalised; every computation is in exact arithmetic in `verify/`. The author used AI tools (Claude, Anthropic; OpenAI Codex), as stated in the paper, and is responsible for its content.


**Version 2** (25 October 2026, tag `strange-operator-twist-v2`): a Codex referee report found that the decomposition `P = I ⋆ Sym² D` is in Bogner and Reiter (2012); v2 credits it and drops the claim of novelty. It also states the integrality of the mirror map and Yukawa coupling as computed, not proved; corrects the count of Laurent models (996 meet both sides of both axes, none has the origin inside its Newton polygon); limits the transfer observation to truncated structures; extends the search for models of `D` to all sixteen reflexive polygons, with its scope stated exactly (`verify/laurent_d/`); and has `run_all.py` check every cached coefficient and exit nonzero if any script's stated output is missing. The twisted integrality, the conditional theorem and the certificates are unchanged.

## Contents

- `paper/`: `bogner.tex` and `bogner.pdf`, with `figs/cover.tex` (the degree four cover).
- `verify/`: `run_all.py` runs every check and asserts every number stated in the paper (about two minutes; `--deep` adds the long certificates). Among the scripts: `prove_symsq.py` and `prove_pullback.py` (the structure, symbolic), `twisted_lambert2.py` (twisted integrality to `d = 110`), `mutants_twist.py` and `dwork_twisted.py` (wrong fields, signs, characters and twist bases must fail), `padic.py` (rational rescalings, with a planted scaling recovered), `certify.py` (exact affine-lattice Frobenius certificates), `prime3_obstruction.py`, `jets_test.py` (integral truncations on `L` do not fix the first constant: the transfer observation), `models_check.py` (elliptic fibrations and moments; `MUTANT=1` must fail). `laurent_d/` (the search for two-variable models of `D` on all sixteen reflexive polygons, with a positive control and the logs of its runs). `K80.json` and `K110.json` cache the Yukawa coefficients computed by `strange.py` (`kcache.py` regenerates them).
- `lean/`: a Lake project pinned to Lean 4.34.0 and Mathlib v4.34.0. `lean/README.md` maps the paper to Lean names, `CheckClaims.lean` prints their axioms, and `scripts/mutants.py` runs the mutation tests.

## Reproduce

```
cd verify && python3 run_all.py            # needs sympy
python3 run_all.py --deep                   # optional, longer
cd ../paper && latexmk -pdf bogner.tex
cd ../lean && lake exe cache get && lake build LeanProofs && lake env lean CheckClaims.lean
```

## Licence

The paper is released under [CC BY 4.0](../LICENSE-PAPERS), the code under the [MIT licence](../LICENSE-CODE).
