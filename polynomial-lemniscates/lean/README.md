# Lean proof sources

Lean 4.34.0; Mathlib is pinned by `lake-manifest.json` to 5ed2965256430c3649e86755f9576b54eca72435 (v4.34.0).
`SOURCE-SNAPSHOT.json` records the development commit and the SHA-256 of every source file in this folder.

    lake exe cache get
    lake build LeanProofs
    lake env lean CheckClaims.lean
    python3 scripts/mutants.py

The paper's statements and their Lean names (all in `LeanProofs/Lemniscates/`):

| Paper | Lean |
|---|---|
| Theorem 1 | `TheoremA.lean`: `Lemniscates.theoremA` |
| Corollary 2 | `Corollaries.lean`: `oval_le_six`, `bernoulli_six` |
| Corollary 3 (second part) | `Corollaries.lean`: `M_eq_iff` |
| Lemma 4 (pairing) | `Pairing.lean`: `real_card_le` |
| Lemma 5 (trace formula) | `TraceFormula.lean`: `trace_eq`, `card_S`, `eval_eq_zero_of_mem`, `mem_S_of_algHom` |
| Lemma 6 (no common factor) | `NoCommon.lean`: `no_common_prime`, `no_common_prime_zero` |
| Lemma 7 (resultants) | `ResTop.lean`: `det_top`, `resultant_top`, `det_subtop`, `resultant_subtop` |
| Proposition 8 (deformation) | `Integral.lean`: `exists_monic`; `Fibre.lean`: `finrank_fibre`, `trace_fibre`; `Deform.lean`: `fibre_multiset` |
| Lemma 9 (growth) and constancy | `GrowthGen.lean`: `growth_level`, `growth_zero`; `Constancy.lean`: `tau_const` (via `Liouville.lean`) |
| Lemma 10 (level zero) | `Level0.lean`: `factor`, `level0` |
| Proposition 11, Theorem 1 coprime case | `CaseI.lean`: `trace_identity`, `caseI` |
| Lemmas 12, 13, shared-root case | `CaseII.lean`: `R_eval_eq_zero`, `R_natDegree_le`, `count_of_R_ne_zero`; `CaseIIb.lean`: `pow_eq`, `nested`, `level_set_infinite`, `empty_of_R_eq_zero` |

One difference from the text: the constancy of the trace polynomial (Section 5) is derived from Liouville's theorem
(`Liouville.lean`) rather than from the degree argument in the paper. The ten points of the (2, 3) example are not
formalised; they are certified in `../verify`.

`Pairing.lean` also contains `fixed_card_le_six`, the eight-solution special case used in an earlier version of the
degree-2 argument; nothing depends on it.
