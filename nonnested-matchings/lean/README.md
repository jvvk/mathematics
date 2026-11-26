# Lean formalisation: what is and is not proved

Lean 4 + Mathlib, namespace `NonNested`, files in `LeanProofs/NonNested/`. Build: `lake exe cache get && lake build`;
`lake env lean CheckClaims.lean` prints the axioms of every result below (recorded in `axiom-validation.txt`). Axioms of
every result below: propext, Classical.choice, Quot.sound. No sorry, no native_decide; `decide` is used only to count
the edges of explicit graphs (`G9`, `K5`) and for index facts.

An edge is a pair `(i, j)` with `1 ≤ i < j ≤ n` (`IsGraph n G`). `Nested`, `Crosses`, `Separated` are the strict
inequalities of the note; `IsNN M` (pairwise disjoint, no nested pair) and `IsSNN M` (`IsNN` and crossing transitive on
`M`); `NoNN k G`, `NoSNN k G`: no such `k`-matching in `G`.

## Proved
| Note | Lean | Scope |
|---|---|---|
| Lemma 4 (at most 8 short edges; equality gives the two short stars) | `short_le_eight`, `short_eq_eight` | all n |
| Lemma 5 (L), (R) | `fence_L`, `fence_R` | all n |
| Theorem 1, upper bound | `f3_upper` | n ≥ 6, given `CPHyp` and `PSHyp` |
| Theorem 1, lower bound (K5 plus fans) | `lowerGraph`, `card_lowerGraph`, `noNN_lowerGraph` | n ≥ 5 |
| Theorem 1: `f_3(n) = f*_3(n) = 2n` | `theorem1` | n ≥ 6, given `CPHyp` and `PSHyp` |
| Theorem 2: `G9` has 28 edges, no strongly non-nested 4-matching | `card_G9`, `noSNN4_G9` | (the note's case proof) |
| Theorem 2: adding a vertex joined to 1, 2, 3 | `noSNN4_addVertex` | all n ≥ 3 |
| Theorem 2: `f*_4(n) ≥ 3n + 1` | `theorem2`, `strong_conjecture_fails` | n ≥ 9 (no hypotheses) |
| Theorem 3, Lemma 9 (c): window `[c−1, c+2]` with `(c−3,c), (c,c+2)` | `lemmaE` | all n, star given |
| Theorem 3, Lemma 9 (a), (b): the two end windows | `endWindowA`, `endWindowB` | all n, star given |
| Theorem 3, Lemma 9 (d): middle window | `lemmaM` | all n, star given |
| Theorem 3, Lemma 9 (e), (f): close pairs at distance 1, 2 | `closePair1`, `closePair2` | all n, star given |
| Theorem 3, Lemma 12: the exceptional arrangement `a, a+4, a+8` | `exceptional` | all n, star given |
| Theorem 3, Lemma 12: the counting step `|F| ≤ 2|X|` | `card_le_two_mul` | general double counting |

## Not formalised (cited theorems, as explicit hypotheses)
- **Capoyleas–Pach** (J. Combin. Theory Ser. B 56 (1992) 9–15), case of no three pairwise crossing chords: `CPHyp`,
  at most `4n − 10` edges for `n ≥ 5`.
- **Pilaud–Santos** (Discrete Comput. Geom. 41 (2009) 284–317, Corollary 4.2(ii) in arXiv:0706.3121): `PSHyp`. For a
  graph with no three pairwise crossing edges and `4n − 10` edges (by `CPHyp`, a 2-triangulation) and every chord
  `{p, p+2}`, there are `u, v` with `p, p+1, p+2, u, v` in cyclic order and the five 2-star chords present.
Only Theorem 1 uses these hypotheses. Theorem 2 uses none.

## Theorem 3 (version 2): what the Lean files cover
`K4Plain.lean` formalises the local star lemmas of Section 4 in the form "given the listed edges of `G` and a
`3`-star on the window whose long chords lie in `G`, `G` has a non-nested `4`-matching": each table row of the note
is one `omega`-checked case (`StarPos` is the cyclic position of `p < q < r`, `StarLongIn` the presence of the long
chords). The centre is written `c = z + 3` so that no natural-number subtraction occurs. Lemma 9(c) is stated with
only `(c−3,c)` and `(c,c+2)`, as in the note. Not formalised in this version: the short-edge lemmas (Lemmas 6 to 8),
the existence of the star (Theorem PS for `k = 3`, cited), the star identification and bridge argument of Lemma 12,
Lemma 13's case split, Lemma 10, and Computations 1 and 2 (certified in `../verify` by two programs each).

## Route differences from the note
- Lemma 4's count picks three disjoint edges directly from five sorted positions (the note now says this too) instead
  of the matching bound for a union of paths.
- Lemma 5 (R) is proved by the mirrored argument with `(a − 1, a)` as the separated edge, not by reversing the order.

## Mutation tests
`scripts/mutants.toml`, run with `cd scripts && python3 mutate.py mutants.toml` (runner included): 20 mutants, all
rejected, all controls pass (12 from version 1, 8 for Theorem 3). Each states a false version of a result: 7 short edges; `b − a ≥ 4`; Lemma 5 with
`i ≤ a − 3`; Theorem 1 with `2n − 1` and with `2n + 1`; `lowerGraph` with `2n + 1` edges and with no non-nested
2-matching; `G9` with 29 edges and with no strongly non-nested 3-matching; the extension with no strongly non-nested
3-matching; Theorem 2 with `3n + 2`; the failure statement at bound `3n + 1`. (The last two are false by the computed
value `f*_4(9) = 28`, verified in `../verify`.) For Theorem 3: Lemma 9(c) with `A, B` from `c+3`; (a) from `c+2`;
(b) from `c+3`; (d) with `A` reaching `c−3`; (e) with `B` from `c+4`; (f) without `(c+2,c+4)`; the exceptional
arrangement with the unit edge inside the window; the counting step with `|F| ≤ |X|`. Each is false by a computed
counterexample (`../verify` and the work folder's checks).
