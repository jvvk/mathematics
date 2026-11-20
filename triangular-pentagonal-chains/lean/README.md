# Lean formalisation

Lean 4.34.0 with Mathlib v4.34.0. Two namespaces with the same structure: `TriChains` (triangular sums,
Theorem 1) and `PentChains` (generalized pentagonal sums, Theorem 2). `PentChains` keeps the names of the
triangular development so that the step file carries over verbatim: there, `IsTri s` means that `s` is a
generalized pentagonal number (`2s = k(3k-1)` for some integer `k`), and `TriChain`, `TriNecklace` are chains and
necklaces with generalized pentagonal adjacent sums.

```
lake exe cache get && lake build LeanProofs && lake env lean CheckClaims.lean
```

`CheckClaims.lean` prints the base hypothesis `BaseHyp` of each namespace, the two headline theorems and their
axioms. Every report is `[propext, Classical.choice, Quot.sound]` (`axiom-validation.txt`).

## What is proved, and what is assumed

The headline theorems are conditional on `BaseHyp`: a good chain exists for every length `54 ≤ N ≤ 2673`
(pentagonal: `60 ≤ N ≤ 2965`). Those 2620 and 2906 chains (3.6 and 4.4 million entries) are too large to state as
Lean data. They are in `../verify/base_chains.txt.gz` and `../pentagonal/verify/base_chains.txt.gz`, regenerate
byte for byte from `base_gen.c`, and are checked by `recheck.py` part (1), which shares no code with the generator.
The nonexistence halves (no chain for `3..8`, no necklace for `3..11` or `14`; pentagonal: no chain for 2 or 3, no
necklace for `3..8`) are exhaustive searches, done twice by different methods in `verify/`, and are not in Lean.

| Paper | Lean (`TriChains` / `PentChains`) | File |
|---|---|---|
| inflation identity `49 T_k + 6 = T_{7k+3}` (pentagonal `49 P_k + 2 = P_{7k-1}`), parity kept | `tri_inflate`, `oddTri_inflate` | `Basic.lean` |
| Lemma (block map `f c` keeps odd triangular sums; reversal) | `oddTri_f`, `chain_map_f`, `chain_reverse` | `Basic.lean` |
| offsets in a window of 49 determine value and offset | `f_window` | `Basic.lean` |
| Proposition (the stitching step, for general `n`): no repeats, length `N`, range `[1, N]`, odd triangular sums, right ends | `step` | `Step.lean` |
| the 98 stitching arrangements are valid | `layout_valid` (one `decide` per arrangement) | `Layouts.lean` |
| small chains and necklaces | `small_chains`, `small_necklaces` | `SmallCases.lean` |
| induction from the base to every `N` | `good_all` | `Main.lean` |
| Theorem 1 / Theorem 2, existence halves | `berlekamp_guy` (conditional on `BaseHyp`) | `Main.lean` |

## Mutation tests

`scripts/trichains_mutants.toml` (12 mutants) and `scripts/pentchains_mutants.toml` (10 mutants), run with
`python3 -I scripts/mutate.py scripts/<suite>.toml` from `lean/` after a build. Each mutant is a stronger
false claim or one corrupted datum (for example `49 T_k + 5` in the identity, a changed arrangement, a small chain
with one entry altered), and each must stop the build. Logs: `trichains-mutation-validation.log` (12/12 rejected, lean-proofs commit 3dbcbe7) and
`pentchains-mutation-validation.log` (10/10, commit 22831b9); the shipped `.lean` files are byte-identical to those commits.

`SOURCE-SNAPSHOT.json` records the lean-proofs commit and a hash of every shipped file.
