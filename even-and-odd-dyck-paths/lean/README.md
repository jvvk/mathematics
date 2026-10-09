# Lean formalisation: even and odd Dyck paths

Lean 4.34.0 with Mathlib v4.34.0. Build with `lake exe cache get && lake build LeanProofs`, then
`lake env lean CheckClaims.lean` prints each result's axioms (only `propext`, `Classical.choice`,
`Quot.sound`) and evaluates the definitions on small cases. `python3 scripts/mutants.py` checks that 12 wrong
variants fail.

The main theorem, in Lean:

```lean
theorem signed_dyck (n k : ℕ) (hn : 1 ≤ n) :
    ∑ P ∈ Dyck n k, (-1 : ℤ) ^ maj P = ((Dyck n k).filter (fun P => rc P = P)).card
```

Here a path is a `List Bool` (`true` = up), `Dyck n k` is the set of paths of length `2n` that stay at height
`≥ 0`, end at `0` and have `k` valleys, `maj` sums the positions of the valley down steps, and `rc` reverses a
path and exchanges up and down.

| Paper | Lean (namespace `QNarayana`) | File |
|---|---|---|
| Lemmas 1 and 2: paths and their words | `dec_flags`, `dec_spec`, `dk_dec`, `okTo_count`, `encW_mem`, `decW_mem` | `Dyck.lean` |
| Equation (3): the sign | `maj_sign` | `Dyck.lean` |
| Lemma 2: mirror images | `flags_rc`, `sym_iff` | `Dyck.lean` |
| Lemma 3: the partner rule | `partner`, `ι`, `partner_facts`, `ι_ι`, `okTo_ι`, `wt2_ι`, `sgn_ι` | `Words.lean` |
| Lemma 3: fixed words and their sign; equation (4) | `F`, `fix_to_F`, `F_to_fix`, `sgn_F`, `signed_sum_eq_card_fix` | `Words.lean` |
| Lemma 4: halving and last departures | `ψ`, `ψ'`, `minRel_half`, `unhalf_half`, `F_unhalf`, `sym_decomp`, `card_Fix_eq_card_Sym` | `Bijection.lean` |
| Theorem 1 | `signed_dyck` | `Dyck.lean` |

Two differences of presentation. The paper's valley coordinates appear in Lean as flag lists: `fu P` records,
for each up step, whether a down step follows it, and `fd P` records, for each down step, whether an up step
follows it; `x ∈ U` exactly when the `x`th up step is a peak with `x < n`, and `x ∈ D` exactly when the `x`th
down step is a valley. The run decoder `dec` rebuilds a path from its flags. Lean counts the weight of a word as
`wt2 = #u + #d + 2#b`, which is `2k` on the words of Lemma 2.

## What is not formalised

- Identity (1) of Fürlinger and Hofbauer, which turns Theorem 1 into the statement about `q`-Narayana numbers at
  `q = -1`. It is quoted from the literature; `verify/recheck/recheck.py` checks it for `n ≤ 8`.
