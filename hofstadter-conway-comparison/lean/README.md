# Lean formalisation: A comparison theorem for the Hofstadter–Conway $10,000 sequence and its alternating variant

Lean 4 (v4.34.0) with Mathlib `v4.34.0`. The sequences `c` and `s` are defined in `Basic.lean` by their
recurrences, with initial values `1, 1`; a call outside `[1, n-1]` returns `0`, and `c_recurrence`,
`s_recurrence` show that this never happens, so both satisfy the recurrences exactly as written. A
binary word is encoded by its prefix-count function. Every theorem below depends only on `propext`,
`Classical.choice` and `Quot.sound` (some on a subset); `Audit.lean` prints the axioms of each one when
it is compiled.

## Build

```
lake exe cache get     # Mathlib build cache
lake build             # compiles every module and runs the axiom audit
./mutants.sh           # sixteen mutants, each rejected; the unchanged copy builds
```

## Where each result is

| Paper | Lean | File |
|---|---|---|
| The sequences `c` and `s` | `c`, `s` | `Basic.lean` |
| Dyck, irreducible and symmetric words | `Dyck`, `Irred`, `Symm` | `Basic.lean` |
| Lemma 2.1 (prefix and letter forms of symmetry) | `symm_iff_letter` | `Corollary.lean` |
| The operators `F`, `G`: thresholds and recurrences (2.2), (2.3) | `ASpec`, `BSpec`, `Arec`, `Brec`, `FP`, `GP`, `FP_spec`, `GP_spec`, `FP_succ`, `GP_succ` | `Ops.lean` |
| Lemma 2.2 (thresholds exist, increments 0 or 1, Dyck outputs; part (5)) | `A_next`, `B_next`, `FP_dyck`, `GP_dyck`, `ASpec.letter_zero` | `Ops.lean` |
| Lemma 2.3 (monotonicity, irreducibility, symmetry) | `FP_mono`, `GP_mono`, `FP_irred`, `FP_symm`, `GP_symm` | `Ops.lean` |
| Lemma 2.4 (the central perturbation `T`) | `TP`, `TP_dyck`, `TP_le`, `TP_symm` | `Tee.lean` |
| Lemma 3.1 (key lemma) | `key` | `Key.lean` |
| Proposition 4.1 (the block words of `c` and `s`) | `blocks` | `Blocks.lean` |
| `c` and `s` satisfy their recurrences, every argument in range | `c_recurrence`, `s_recurrence` | `Main.lean` |
| Corollary 4.2 (`s(2^k) = c(2^k) = 2^(k-1)`, `s` slow, the sign of `s(n) - n/2`) | `c_s_pow`, `s_slow`, `s_sign` | `Corollary.lean` |
| Lemma 4.3 (`w_k` symmetric and irreducible, `v_k` symmetric) | `w_props`, `v_symm` (and `v_dyck`) | `Blocks.lean` |
| Section 5 and Remark 1 (`v_k ≤ T(w_k)` for odd `k ≥ 3`) | `odd_blocks` | `Main.lean` |
| **Theorem 1** | `main` (`n ≤ c n + s n` and `s n ≤ c n`), `hofstadter_conway_dominates` (the form in the paper, over `ℚ`) | `Main.lean` |

The proofs follow the paper. The base case `T(w_3) = v_3` is checked by `decide` on words of length 8,
the same small check the paper does by hand; nothing else is decided by computation.

## Mutation tests

`./mutants.sh` copies the sources to `HofstadterConway/Mut`, plants a single wrong change (in the
definitions of `c` and `s`, the recurrences (2.2) and (2.3), the perturbation `T`, the key lemma, the
odd-block bound, Theorem 1, Lemma 2.1, Corollary 4.2 or Lemma 4.3) and builds the copy. All sixteen mutants are
rejected, and the unchanged copy builds.
