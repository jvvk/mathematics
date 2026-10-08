# Lean proof sources

Lean 4.34.0; Mathlib is pinned by lake-manifest.json to
5ed2965256430c3649e86755f9576b54eca72435 (v4.34.0).
SOURCE-SNAPSHOT.json records the development commit and the hash of every file. Build caches are excluded.

    lake exe cache get
    lake build LeanProofs
    lake env lean CheckClaims.lean
    python3 scripts/mutants.py

| Paper | Lean |
|---|---|
| The model: lengths and turns as functions on `Fin`, displacement `Z`, optimality over all permutations | `Basic.lean`: `θ`, `Z`, `Optimal`, `Admissible` |
| The three moves (length swap, adjacent turn swap, first segment to the end) | `Moves.lean`: `Z_swap_lengths`, `Z_swap_turns`, `Z_head`, `Z_rot` |
| `0 < φ < T` | `Support.lean`: `arg_pos`, `arg_lt_T` |
| Lemma 2.1 (support) | `Exchange.lean`: `support`, `support_eq` |
| Lemma 2.2 (length exchange) | `Exchange.lean`: `length_cmp`; `Structure.lean`: `lt_iff_closer` |
| Lemma 2.3 (turn exchange) | `Exchange.lean`: `turn_cmp` |
| Theorem 1, parts 1-4, first and last turns | `Structure.lean`: `lengths_unimodal`, `shortest_at_end`, `half_lt_arg`, `endpoint_arg`, `last_second_shortest`, `turns_valley`, `longest_at_smallest_turn`, `first_turn_descends`, `last_turn_ascends` |
| Proposition 5.1 (`a₄ = 3`) | `N4.lean`: `n4_classify`; `Witness.lean`: `witness_P1`-`P3`, `a4_eq_three` |

Not formalised: Theorem 2 (algorithm), Proposition 6.1, Theorem 4 (realisation) and the witnesses for
n >= 5, which are checked by the exact programs in `../verify`. Every result uses only propext,
Classical.choice and Quot.sound (axiom-validation.txt); isolated build in build-validation.log.
