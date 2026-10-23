# Lean formalisation: Fences do not maximise orbits of linear extensions

Lean 4 (v4.34.0) with Mathlib. Every theorem below depends only on `propext`, `Classical.choice` and
`Quot.sound`; `LeanProofs/Orbits516140/Report.lean` prints the axioms of the headline results when it is
compiled, and `CheckClaims.lean` restates them.

Conventions. A linear extension is an order-preserving bijection `α ≃ Fin n` (`LinExt α`), and
`orbitCount α` is the number of orbits of `α ≃o α` on them. A disjoint union of fences is encoded as
`IsFenceUnion α`: the elements can be listed so that comparable elements are adjacent in the list. Every
disjoint union of fences has such a listing (each fence in zigzag order, one after another), so the Lean
hypothesis is no stronger than the paper's and Theorem 2 as formalised implies the paper's statement. The
threshold `J n` is the least `j` with `n ≤ 2^j + j − 1`, as in the paper.

| Paper | Lean | File |
|---|---|---|
| Free action, `f = e/#Aut` | `stabilizer_eq_bot`, `card_linExt_eq`, `orbitCount_eq_div` | `Basic.lean` |
| First case, `n = 8`: `e(Q + •) = 2384`, trivial automorphisms, not a fence union; `Z_4 + Z_2 + 2•` has `f = 2100` | `e_Q1`, `aut_Q1`, `orbits_Q1`, `Q1_not_fenceUnion`, `orbits_F`, `F_isFenceUnion`, `orbits_F_lt_Q1` | `Posets.lean` |
| `Q` and `R` of Theorem 1: `e(Q) = 298`, `e(R) = 1613`, automorphisms, duality | `e_Q`, `aut_Q`, `Q_not_selfDual`, `e_R`, `aut_R`, `R_selfDual` | `Posets.lean` |
| Lemma 1 (`t` disjoint pairs: `2^t e ≤ n!`) | `two_pow_mul_card_linExt_le` | `Fences.lean` |
| `k` isolated points: `k! ≤ #Aut` | `factorial_le_card_aut` | `Fences.lean` |
| A fence union has `t` disjoint pairs and `k` isolated points with `n ≤ 3t + k` | `exists_matching` | `Fences.lean` |
| Proposition 2, in the form `f · 2^t · k! ≤ n!` with `n ≤ 3t + k` | `orbitCount_mul_le` | `Fences.lean` |
| Lemma 3 (Graham's construction: `f ≥ m!`) | `Gr.orbitCount_Gr`, `exists_poset_orbitCount_ge`, `exists_poset_orbitCount_ge'` | `Fences.lean` |
| Inequality (2) and its consequence, for `n ≥ 181` | `factorial_lt` | `Fences.lean` |
| **Theorem 2** for `n ≥ 181` | `fence_union_not_max`, `fence_union_not_max'` | `Fences.lean` |

Route and differences from the paper.

- Lemma 1 is proved by injection, not probability: composing with the transposition of one pair maps the
  bijections that respect it injectively onto a disjoint set of bijections, one pair at a time.
- Proposition 2 is used through the matching: in each run of comparable neighbours of the listing, take the
  positions where the run length so far is odd. This gives `n ≤ 3t + k` directly.
- Lemma 3 is proved without the paper's nonempty condition on the subsets (`exists_poset_orbitCount_ge'`,
  `1 ≤ m ≤ 2^j`): it needs only that the full set of tops is one of the subsets. The paper's form
  (`m ≤ 2^j − 1`) follows.
- Inequality (2) goes through `2 (n)_J^3 ≤ 2 n^(3J) < 2^n ≤ 2 (2^t k!)^3`, with a finite check on
  `[181, 255]` and `3(r + 1)^2 + 1 ≤ 2^r` for `r ≥ 8` above it. The threshold 181 is the true threshold of this route.

Not formalised: Theorem 1 (the exhaustive search over all posets with `n ≤ 11`) and the range `58 ≤ n ≤ 180`
of Theorem 2, both exact computations checked by `../verify/`.

## Build

```
lake exe cache get                                  # Mathlib build cache
lake build                                          # compiles every module and prints the axiom audit
lake env lean CheckClaims.lean                      # restates each headline result and its axioms
python3 scripts/mutate.py scripts/mutants.toml      # 61 mutants, each rejected (rebuilds per mutant)
```
