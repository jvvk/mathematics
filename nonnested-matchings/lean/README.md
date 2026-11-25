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
| Lemma 3 (at most 8 short edges; equality gives the two short stars) | `short_le_eight`, `short_eq_eight` | all n |
| Lemma 4 (L), (R) | `fence_L`, `fence_R` | all n |
| Theorem 1, upper bound | `f3_upper` | n ≥ 6, given `CPHyp` and `PSHyp` |
| Theorem 1, lower bound (K5 plus fans) | `lowerGraph`, `card_lowerGraph`, `noNN_lowerGraph` | n ≥ 5 |
| Theorem 1: `f_3(n) = f*_3(n) = 2n` | `theorem1` | n ≥ 6, given `CPHyp` and `PSHyp` |
| Theorem 2: `G9` has 28 edges, no strongly non-nested 4-matching | `card_G9`, `noSNN4_G9` | (the note's case proof) |
| Theorem 2: adding a vertex joined to 1, 2, 3 | `noSNN4_addVertex` | all n ≥ 3 |
| Theorem 2: `f*_4(n) ≥ 3n + 1` | `theorem2`, `strong_conjecture_fails` | n ≥ 9 (no hypotheses) |

## Not formalised (cited theorems, as explicit hypotheses)
- **Capoyleas–Pach** (J. Combin. Theory Ser. B 56 (1992) 9–15), case of no three pairwise crossing chords: `CPHyp`,
  at most `4n − 10` edges for `n ≥ 5`.
- **Pilaud–Santos** (Discrete Comput. Geom. 41 (2009) 284–317, Corollary 4.2(ii) in arXiv:0706.3121): `PSHyp`. For a
  graph with no three pairwise crossing edges and `4n − 10` edges (by `CPHyp`, a 2-triangulation) and every chord
  `{p, p+2}`, there are `u, v` with `p, p+1, p+2, u, v` in cyclic order and the five 2-star chords present.
Only Theorem 1 uses these hypotheses. Theorem 2 uses none.

## Route differences from the note
- Lemma 3's count picks three disjoint edges directly from five sorted positions (the note now says this too) instead
  of the matching bound for a union of paths.
- Lemma 4 (R) is proved by the mirrored argument with `(a − 1, a)` as the separated edge, not by reversing the order.

## Mutation tests
`scripts/mutants.toml`, run with `cd scripts && python3 mutate.py mutants.toml` (runner included): 12 mutants, all
rejected, all controls pass. Each states a false version of a result: 7 short edges; `b − a ≥ 4`; Lemma 4 with
`i ≤ a − 3`; Theorem 1 with `2n − 1` and with `2n + 1`; `lowerGraph` with `2n + 1` edges and with no non-nested
2-matching; `G9` with 29 edges and with no strongly non-nested 3-matching; the extension with no strongly non-nested
3-matching; Theorem 2 with `3n + 2`; the failure statement at bound `3n + 1`. (The last two are false by the computed
value `f*_4(9) = 28`, verified in `../verify`.)
