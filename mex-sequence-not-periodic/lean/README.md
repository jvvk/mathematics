# Lean formalisation: A mex sequence that is not ultimately periodic

Lean 4 (v4.34.0) with Mathlib `v4.34.0`, about 550 lines. A mex sequence is a function
`a : ℕ → ℕ` with `a 0, …, a 7 = 1,1,1,0,1,0,1,1` and `a (n+1) = mex {a i + a (n-i) : i ≤ n}`
for `n ≥ 7` (`IsMex` in `Basic.lean`). Every theorem below depends only on `propext`,
`Classical.choice` and `Quot.sound`; `Audit.lean` prints the axioms of each one when it is compiled.

## Build

```
lake exe cache get     # Mathlib build cache
lake build             # compiles every module and runs the axiom audit
```

## Where each result is

| Paper | Lean | File |
|---|---|---|
| Lemma 1 (the zeros) | `zeros` | `MexSequence/Twins.lean` |
| Lemma 2 (the twins agree; each new twin value differs from every earlier one) | `twins` | `MexSequence/Twins.lean` |
| Theorem 1, by the route of Section 4 | `unbounded_of_twins`, `not_eventually_periodic_of_twins` | `MexSequence/Twins.lean` |
| Lemma 3 and Theorem 2 (the closed form `F` is a mex sequence, and the only one with this start) | `isMex_F`, `eq_F` | `MexSequence/Main.lean` |
| Theorem 1 again, from the closed form | `unbounded`, `not_eventually_periodic` | `MexSequence/Main.lean` |

`Twins.lean` follows the paper's proof and never uses the closed form. `Main.lean` checks the closed
form against the rule: positions below 60 by evaluation (`decide`), the rest by a symbolic case
analysis on residues (`Arith.lean`), organised differently from the proof in Appendix A.

Not formalised: the remarks of Section 5 (the zero sets and greedy sum-free sets, the search, the
second example).

## Mutation tests

`./mutants.sh` copies the sources, plants one wrong change (a slope, a starting term, a residue, the
claim of Lemma 1 or 2) and checks that the copy no longer compiles. All ten mutants are rejected.
