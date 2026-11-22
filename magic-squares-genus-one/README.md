# Genus-one curves on the magic-square-of-squares surface

<!-- visual:start -->
<p align="center"><img src="https://raw.githubusercontent.com/jvvk/jvvk/081160626ecf30d9db28edae774310fb5108893c/assets/msos-genus1.svg" width="760" alt="Genus-one curves on the magic-square-of-squares surface"></p>

<p align="center"><b>Three-by-three magic squares of squares are the rational points of a surface V in P⁸. Its only curves of geometric genus one and degree at most six are the sixteen known quartics on which the centre entry vanishes.</b><br><sub>New partial result · every exclusion recomputed by independently written code; group-law and last-stage exclusions certified · no Lean</sub></p>

<p align="center"><sub><a href="paper">paper</a> · <a href="verify">code</a> · <a href="../">all results</a></sub></p>
<!-- visual:end -->

Nobody knows whether a 3×3 magic square can have nine distinct perfect squares as entries. Such squares are the rational points of a surface `V ⊂ P⁸`. Michaud-Rodgers ([Warwick dissertation, 2019](https://warwick.ac.uk/fac/sci/maths/people/staff/michaud/fourthyearproject.pdf)) found its 256 singular points and showed it contains no lines; Auel and Singer ([arXiv:2609.09351](https://arxiv.org/abs/2609.09351)) showed that it is of general type, cut out by six quadrics, and that the hyperplane section where the centre entry vanishes is the union of sixteen elliptic quartics. Bruin, Thomas and Várilly-Alvarado ([Algebra Number Theory 16 (2022)](https://doi.org/10.2140/ant.2022.16.1377)) proved that `V` contains only finitely many curves of genus zero or one, without listing them. By the Bombieri–Lang conjecture these curves would carry all but finitely many rational points.

This note proves:

- **Theorem 1.1.** Every irreducible curve on `V` whose normalisation has genus one and whose degree is at most six is one of the sixteen quartics in the hyperplane `t₀₀ = 0`.
- **Section 7.** In degree seven the same method reduces the 8280 admissible configurations to 110, all of one shape; those 110 stay open.

The proof attaches to such a curve four rational functions, one for each line through the centre of the square, and derives necessary conditions on their divisors: a genus-five subfield obstruction, forced ramification at the zeros of the centre coordinate, the group law, and a square-class obstruction for pencils of degree two. Degree four needs no computer. In degrees five and six every configuration is excluded, in exact arithmetic, by two independently written implementations; every group-law exclusion, and every exclusion among the 202 degree-six tables that reach the last stage of the first implementation, carries a certificate checked by separate code.

Preprint v1, 22 November 2026, not peer reviewed; released before the author's line-by-line reading. Zenodo: [doi:10.5281/zenodo.24441957](https://doi.org/10.5281/zenodo.24441957), identical to this folder at tag `magic-squares-genus-one-v1`. No part is formally verified in Lean: the steps rest on Riemann–Hurwitz, function fields of elliptic curves and the group law, which Mathlib cannot yet express in this form. The author used AI tools (Claude, Anthropic; Codex, OpenAI) in this work, as the paper's declaration describes step by step, and is responsible for its content.

**Earlier and parallel work.** Dzoba's unrefereed document E1-DIFFERENTIALS.md (github.com/dzoba/magic-squares-of-squares, commit `aa23aa9`, 24 October 2026; the repository was no longer public on 26 October 2026) shows that every rational curve on `V` is one of Auel and Singer's 128 conics, excludes parts of the genus-one problem, and bounds the degree of the plane image of a genus-one curve by 153. Our independent check of its Theorem 6.4 is in `verify/thm64-dzoba/`; the document itself carries no licence and is not redistributed. The MagicNumbers project reached the conic classification independently (September 2026). For the analogous cuboid surface, Stoll and Testa ([arXiv:1009.0388](https://arxiv.org/abs/1009.0388)) classified all integral curves of degree at most six.

## Contents

- `paper/`: `genus1.tex` and `genus1.pdf`.
- `verify/` (Python 3 with [SymPy](https://www.sympy.org/); `residue_claude.py` also needs [Singular](https://www.singular.uni-kl.de/)):
  - `run_chain.sh`: deletes every generated data file, regenerates all of them and runs every filter and audit, in order. About 5 minutes.
  - `check_claims.py`: asserts every count in the paper (Table 1, the group-law certificates, and the degree-seven numbers 8280, 530, 296, 100, 24, 110) from the outputs of the programs below. About 2 minutes. `mutants.toml` plants 11 wrong claims, run by `mutate.py`; each must make `check_claims.py` fail with a `FAIL` verdict (a crash counts as inconclusive, not as a rejection).
  - The enumeration, written twice: `mconfigs.py` (a recursion over columns) and `enum_indep.py` (a meet-in-the-middle search over row sums). They give identical sets of tables in degrees four to seven, and `enum_indep.py` runs the whole chain of conditions on its own tables.
  - The certifying filters: `pipeline.py` with `rh_filter.py`, `rh_grouplaw.py` and `grouplaw_exact.py` (forced ramification and the group law), `centre_distinct.py` (Propositions 3.1 and 3.3), `centre_sextic.py` (the conditions of Section 4 with all six pairs, and Lemmas 5.1 to 5.3; writes `m6_centre_sextic_certificates.json`), `grouplaw_certificates.py` (a certificate for every group-law exclusion in degrees five and six: 93 and 2075, all integer combinations except 31 torsion cases of degree six, using `torsion_certificates.py`), checked by `check_grouplaw_certificates.py`, which recomputes the full-fibre rows with the other implementation's forced values.
  - The independent re-implementation and audits: `audit_sextic.py` (forced values from leading coefficients, a different method; same reason for every one of the 202 degree-six tables), `check_centre_distinct_algebra.py`, `check_centre_sextic_algebra.py` and `verify_sec5.py` (the algebra of Lemmas 3.2 and 5.3, by two separate exact computations).
  - Degree seven: `centre_septic.py` with the audits `check_centre_septic.py` and `check_septic_claude.py` (residual fibre, packing, tame reciprocity: 530 to 234); `m7_targets.py` (writes the split of the 234 into 60 tables with a degree-two pair monomial and 174 others, and the 134 left after the residue condition); `offcentre_residue.py` with `check_offcentre_residue.py` (the residue condition: 174 to 74), and `residue_claude.py --expect-unit`, which confirms each of the 100 residue exclusions by a direct Gröbner basis in Singular and fails otherwise; `septic_jet_filter.py` with `check_septic_jets.py`, and `jets_claude.py` (jets: 134 to 110).
  - `thm64-dzoba/`: the independent check of Dzoba's Theorem 6.4 (rational curves on `V` are the 128 conics), with its own notes in `VERIFY_THM64.md`. Needs SymPy and [PARI/GP](https://pari.math.u-bordeaux.fr/).
  - The `.json` files are the outputs of `run_chain.sh` (configurations, survivors and certificates, named by degree `m4` to `m7`, and the two `*_claude_*.json` verdict files).

## Reproduce

```
cd verify && ./run_chain.sh && python3 check_claims.py
cd thm64-dzoba && python3 eta_regular.py && python3 curves.py && python3 gaps.py && python3 mutants.py && gp -q pari_check.gp < /dev/null
cd ../../paper && latexmk -pdf genus1.tex
```

The mutation suite rewrites data files, so run it on a copy: `cp -R verify /tmp/v && python3 /tmp/v/mutate.py /tmp/v/mutants.toml` (about 25 minutes). `thm64-dzoba/mutants.py` takes about 4 minutes.

## Licence

The paper is released under [CC BY 4.0](../LICENSE-PAPERS), the code under the [MIT licence](../LICENSE-CODE).
